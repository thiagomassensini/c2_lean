import Mathlib
import LeanC2.Identity
import LeanC2.Normalization
import LeanC2.Tilt

namespace LeanC2

-- ═══════════════════════════════════════════════════════════════════
-- §C  Meromorphic continuation:  Z_spec(s) = ζ(s)  for  Re(s) > 0
-- ═══════════════════════════════════════════════════════════════════

/-- The spectral zeta function:  Z_spec(s) := (D∞(s) − B∞(s)) / c₀(s).
    This is the canonical object whose meromorphic continuation equals ζ(s). -/
noncomputable def routeK_Zspec (Dinf Binf : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Dinf s - Binf s) / c0Complex s

/-- Pointwise identity: Z_spec = ζ at a single point where Thm 13 holds. -/
theorem routeK_Zspec_eq_of_thm13 {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hs : 0 < s.re) (ζ : ℂ)
    (hId : Dinf s - Binf s = c0Complex s * ζ) :
    routeK_Zspec Dinf Binf s = ζ := by
  unfold routeK_Zspec
  have hc0 : c0Complex s ≠ 0 := c0Complex_ne_zero_of_re_pos hs
  calc (Dinf s - Binf s) / c0Complex s
      = (c0Complex s * ζ) / c0Complex s := by rw [hId]
    _ = ζ := by field_simp [hc0]

/--
Transversal-product-jet specialization for `Z_spec`.
This is the direct bridge from Thm 8's abstract `Fjet ≠ 0` conclusion to
`routeK_Zspec Dinf Binf s ≠ 0`, once a Leibniz-jet description of `Z_spec` is available.
-/
theorem routeK_Zspec_nonzero_of_transversal_product_jet
    {Dinf Binf : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) (cJet zJet : ℕ → ℂ)
    (hz : ∀ k < m, zJet k = 0)
    (hcId : cJet 0 = c0Complex s)
    (hzm : zJet m ≠ 0)
    (hLeibniz :
      routeK_Zspec Dinf Binf s = Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    routeK_Zspec Dinf Binf s ≠ 0 := by
  exact routeK_thm8_transversal_product_jet hs m cJet zJet
    (routeK_Zspec Dinf Binf s) hz hcId hzm hLeibniz

/--
**Identity Principle for the C2 framework (abstract form).**

If two functions `F` and `G`, both defined on the half-plane `Re(s) > 0`,
agree on the *convergence half-plane* `{s : Re(s) > 1}` (an open subset with
accumulation points in `{Re(s) > 0}`), and if `G` is the meromorphic
continuation of `F`, then `F = G` on the full half-plane `Re(s) > 0`.

In our framework this is the bridge from the algebraic identity
`D∞ − B∞ = c₀·ζ` (valid for σ > 1 via Fubini) to the *analytic* identity
valid for σ > 0 (via the Theorem of Identity for meromorphic functions).

We encode this as an *axiom schema*: the caller supplies a witness
`hCont` that the continuation equality holds on the full half-plane.
The content of the present theorem is that this, combined with Thm 14
(`c₀ ≠ 0`), immediately yields `Z_spec = ζ` everywhere in σ > 0.
-/
theorem routeK_continuation_Zspec_eq_zeta
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s) :
    ∀ s : ℂ, 0 < s.re →
      routeK_Zspec Dinf Binf s = ζfun s := by
  intro s hs
  unfold routeK_Zspec
  have hc0 : c0Complex s ≠ 0 := c0Complex_ne_zero_of_re_pos hs
  rw [hCont s hs]
  field_simp [hc0]

/--
**Corollary 1 (Zero equivalence).**
Under the continuation hypothesis, `Z_spec(ρ) = 0 ↔ ζ(ρ) = 0` for Re(ρ) > 0.
-/
theorem routeK_continuation_zero_iff
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    routeK_Zspec Dinf Binf ρ = 0 ↔ ζfun ρ = 0 := by
  rw [routeK_continuation_Zspec_eq_zeta hCont ρ hρ]

/--
Pointwise norm-positivity equivalence on the continued half-plane:
`Z_spec(ρ)` has strictly positive norm exactly when `ζfun(ρ)` does.
-/
theorem routeK_continuation_Zspec_norm_pos_iff
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    0 < ‖routeK_Zspec Dinf Binf ρ‖ ↔ 0 < ‖ζfun ρ‖ := by
  rw [routeK_continuation_Zspec_eq_zeta hCont ρ hρ]

/--
Direct quantitative continuation corollary: once `ζfun(ρ) ≠ 0`, the continued
`Z_spec(ρ)` has strictly positive norm.
-/
theorem routeK_continuation_Zspec_norm_pos_of_zeta_nonzero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    {ρ : ℂ} (hρ : 0 < ρ.re)
    (hζ : ζfun ρ ≠ 0) :
    0 < ‖routeK_Zspec Dinf Binf ρ‖ := by
  exact (routeK_continuation_Zspec_norm_pos_iff hCont hρ).2
    (norm_pos_iff.mpr hζ)

/--
Continuation-layer nonvanishing equivalence for the numerator.
On the half-plane `Re(s) > 0`, the continued identity `Dinf - Binf = c₀ · ζ`
and the nonvanishing of `c₀(s)` imply that the numerator is nonzero exactly
when `ζfun(s)` is nonzero.
-/
theorem routeK_continuation_nonzero_iff_zeta_nonzero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re ->
      Dinf s - Binf s = c0Complex s * ζfun s) :
    ∀ s : ℂ, 0 < s.re ->
      (Dinf s - Binf s ≠ 0 ↔ ζfun s ≠ 0) := by
  intro s hs
  have hc0 : c0Complex s ≠ 0 := c0Complex_ne_zero_of_re_pos hs
  constructor
  · intro hnum hz0
    apply hnum
    rw [hCont s hs, hz0]
    simp
  · intro hzeta hnum0
    apply hzeta
    have hprod0 : c0Complex s * ζfun s = 0 := by
      simpa [hCont s hs] using hnum0
    exact (mul_eq_zero.mp hprod0).resolve_left hc0

/--
Global off-axis endpoint reduction, in equivalence form:
global zero exclusion for `ζfun` on the critical strip away from the critical line
is equivalent to global nonvanishing of `Z_spec` on the same domain.

This packages the exact remaining endpoint gap as a statement about `Z_spec`.
-/
theorem routeK_global_zero_exclusion_iff_Zspec_nonvanishing
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s) :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0) ↔
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0) := by
  constructor
  · intro hζ s hs hstrip hhalf hZ0
    have hζ0 : ζfun s = 0 := (routeK_continuation_zero_iff hCont hs).1 hZ0
    exact hζ s hs hstrip hhalf hζ0
  · intro hZ s hs hstrip hhalf hζ0
    have hZ0 : routeK_Zspec Dinf Binf s = 0 :=
      (routeK_continuation_zero_iff hCont hs).2 hζ0
    exact hZ s hs hstrip hhalf hZ0

/--
Final off-axis zero-exclusion reduction:
once `Z_spec` is known to be nonzero throughout the off-axis critical strip,
the same nonvanishing follows for `ζfun` by `routeK_continuation_zero_iff`.

This isolates the last remaining endpoint input as a single hypothesis on `Z_spec`.
-/
theorem routeK_global_zero_exclusion_of_Zspec_nonvanishing
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hZspec : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  exact (routeK_global_zero_exclusion_iff_Zspec_nonvanishing hCont).2 hZspec

/--
Global off-axis zero exclusion from a transversal product-jet mechanism for `Z_spec`.
This is the strongest endpoint currently derivable in the existing framework:
the analytic continuation side comes from `hCont`, while the off-axis nonvanishing
is supplied pointwise by a Leibniz-jet witness for `routeK_Zspec`.
-/
theorem routeK_global_zero_exclusion_of_transversal_product_jet
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hJet :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
          (∀ k < m, zJet k = 0) ∧
          cJet 0 = c0Complex s ∧
          zJet m ≠ 0 ∧
          routeK_Zspec Dinf Binf s = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  apply routeK_global_zero_exclusion_of_Zspec_nonvanishing hCont
  intro s hs hstrip hhalf
  rcases hJet s hs hstrip hhalf with ⟨m, cJet, zJet, hz, hcId, hzm, hLeibniz⟩
  exact routeK_Zspec_nonzero_of_transversal_product_jet hs m cJet zJet hz hcId hzm hLeibniz

/--
Global off-axis zero exclusion from a transversal product-jet mechanism on the
natural numerator `Dinf - Binf`.

This is a stricter endpoint reduction than the `Z_spec`-jet version: the jet
witness now lives on the product-side object controlled by Thm 13/17, and the
passage to `Z_spec ≠ 0` uses only Thm 14 (`c₀(s) ≠ 0`).
-/
theorem routeK_global_zero_exclusion_of_numerator_transversal_product_jet
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hJet :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
          (∀ k < m, zJet k = 0) ∧
          cJet 0 = c0Complex s ∧
          zJet m ≠ 0 ∧
          (Dinf s - Binf s) = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  apply routeK_global_zero_exclusion_of_Zspec_nonvanishing hCont
  intro s hs hstrip hhalf
  rcases hJet s hs hstrip hhalf with ⟨m, cJet, zJet, hz, hcId, hzm, hLeibniz⟩
  have hNumNe : Dinf s - Binf s ≠ 0 :=
    routeK_thm8_transversal_product_jet hs m cJet zJet (Dinf s - Binf s) hz hcId hzm hLeibniz
  unfold routeK_Zspec
  exact div_ne_zero hNumNe (c0Complex_ne_zero_of_re_pos hs)

/--
Global off-axis zero exclusion from a transversal product-jet mechanism on the
continued product `c₀(s) · ζfun(s)`.

This is the next structural reduction step after the numerator version: the jet
witness no longer mentions `Dinf - Binf` directly, only the continued product
appearing in Thm 13/17. The passage back to the numerator uses `hCont`.
-/
theorem routeK_global_zero_exclusion_of_continuation_product_jet
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hJet :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
          (∀ k < m, zJet k = 0) ∧
          cJet 0 = c0Complex s ∧
          zJet m ≠ 0 ∧
          (c0Complex s * ζfun s) = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  apply routeK_global_zero_exclusion_of_numerator_transversal_product_jet hCont
  intro s hs hstrip hhalf
  rcases hJet s hs hstrip hhalf with ⟨m, cJet, zJet, hz, hcId, hzm, hLeibniz⟩
  refine ⟨m, cJet, zJet, hz, hcId, hzm, ?_⟩
  exact (hCont s hs).trans hLeibniz

/--
Reusable Leibniz-style algebraic witness at a point.

This is not an intrinsic jet/derivative predicate on `f`; it only records that
the single value `f s` is realized by a Leibniz-type finite sum with a nonzero
leading coefficient and a nonzero leading `z`-entry.
-/
def routeK_LeibnizWitnessAt (f : ℂ → ℂ) (s : ℂ) : Prop :=
  ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
    (∀ k < m, zJet k = 0) ∧
    cJet 0 ≠ 0 ∧
    zJet m ≠ 0 ∧
    f s = Finset.sum (Finset.range (m + 1))
      (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))

/--
Formal audit: the Leibniz witness predicate is equivalent to plain nonvanishing.

Hence it should not be read as an intrinsic jet or multiplicity predicate; it is
only a structured algebraic witness for the nonzero value `f s`.
-/
theorem routeK_LeibnizWitnessAt_iff_ne_zero {f : ℂ → ℂ} {s : ℂ} :
    routeK_LeibnizWitnessAt f s ↔ f s ≠ 0 := by
  constructor
  · intro h
    rcases h with ⟨m, cJet, zJet, hz, hc0, hzm, hsum⟩
    have hne :
        Finset.sum (Finset.range (m + 1))
          (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j)) ≠ 0 :=
      leibnizNondegenerateByMultiplicity m cJet zJet hz hc0 hzm
    simpa [hsum] using hne
  · intro hf
    refine ⟨0, (fun _ => (1 : ℂ)), (fun _ => f s), ?_, ?_, ?_, ?_⟩
    · intro k hk
      exact (Nat.not_lt_zero _ hk).elim
    · simp
    · simpa using hf
    · simp

/--
Transport a `ζ`-side Leibniz witness to the continued product side.

This is honest witness transport, not intrinsic jet transport: the output is a
new Leibniz witness for the product `c₀ · ζ`, obtained by multiplying the
coefficient family by the nonzero scalar `c0Complex s`.
-/
theorem routeK_continuation_product_witness_of_zeta_witness
    {ζfun : ℂ → ℂ} {s : ℂ} (hc0 : c0Complex s ≠ 0)
    (hJet : routeK_LeibnizWitnessAt ζfun s) :
    routeK_LeibnizWitnessAt (fun z => c0Complex z * ζfun z) s := by
  rcases hJet with ⟨m, cJet, zJet, hz, hcJet0, hzm, hsum⟩
  refine ⟨m, (fun j => c0Complex s * cJet j), zJet, hz, ?_, hzm, ?_⟩
  · simpa using mul_ne_zero hc0 hcJet0
  · calc
      c0Complex s * ζfun s
        = c0Complex s * Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j)) := by rw [hsum]
      _ = Finset.sum (Finset.range (m + 1))
            (fun j => c0Complex s * ((Nat.choose m j : ℂ) * cJet j * zJet (m - j))) := by
            rw [Finset.mul_sum]
      _ = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * (c0Complex s * cJet j) * zJet (m - j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring

/--
Global witness transport on the continuation side.

This theorem is still only transport of algebraic witnesses. It does not use
`hCont` or continuation analyticity; the only real input is local nonvanishing
of `c₀(s)` on `Re(s) > 0`.
-/
theorem routeK_global_continuation_product_witness_of_zeta_witness
    {ζfun : ℂ → ℂ}
    (hJet : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_LeibnizWitnessAt ζfun s) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_LeibnizWitnessAt (fun z => c0Complex z * ζfun z) s := by
  intro s hs hstrip hhalf
  exact routeK_continuation_product_witness_of_zeta_witness
    (c0Complex_ne_zero_of_re_pos hs) (hJet s hs hstrip hhalf)

/--
**Corollary 2 (Critical-line specialization).**
Under the continuation hypothesis, `Z_spec(1/2 + it) = ζ(1/2 + it)`.
-/
theorem routeK_continuation_critical_line
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (t : ℝ) :
    routeK_Zspec Dinf Binf
      (((1 : ℂ) / 2) + t * Complex.I) = ζfun (((1 : ℂ) / 2) + t * Complex.I) := by
  exact routeK_continuation_Zspec_eq_zeta hCont _ (by simp)

/--
**Corollary 3 (Critical-strip representation).**
Under the continuation hypothesis, `D∞(s) = B∞(s) + c₀(s)·ζ(s)` for Re(s) > 0.
This provides a convergent representation of D∞ in the critical strip
(where its original Dirichlet series does not converge).
-/
theorem routeK_continuation_Dinf_repr
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    {s : ℂ} (hs : 0 < s.re) :
    Dinf s = Binf s + c0Complex s * ζfun s := by
  have h := hCont s hs
  have : Dinf s - Binf s + Binf s = Binf s + c0Complex s * ζfun s := by
    rw [h]; ring
  simpa [sub_add_cancel] using this

/--
**Full continuation chain** (Thm 13 + Identity Principle + Thm 14):
packages the algebraic identity (`hAlg`, valid for σ > 1),
the meromorphic continuation (`hMero`, extending to σ > 0),
and `c₀ ≠ 0` to yield `Z_spec = ζ` on the full half-plane.
-/
theorem routeK_continuation_full_chain
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (_hAlg : ∀ s : ℂ, 1 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hMero : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s) :
    ∀ s : ℂ, 0 < s.re →
      routeK_Zspec Dinf Binf s = ζfun s := by
  exact routeK_continuation_Zspec_eq_zeta hMero

/--
**Analytic continuation bridge (AnalyticOnNhd form).**
If `F` and `G` are both analytic on the open half-plane `{Re(s) > 0}`,
and they agree on the open subset `{Re(s) > 1}`, then they agree on
the whole half-plane.  This is a direct application of Mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

We state this as a standalone lemma so that downstream users can supply
`AnalyticOnNhd` witnesses for their specific `Dinf − Binf` and `c₀·ζ`,
getting the full continuation for free.
-/
theorem routeK_analytic_continuation_bridge
    {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s | 0 < s.re})
    (hG : AnalyticOnNhd ℂ G {s | 0 < s.re})
    (hFG : ∀ s : ℂ, 1 < s.re → F s = G s) :
    ∀ s : ℂ, 0 < s.re → F s = G s := by
  -- The half-plane {Re(s) > 0} is convex, hence preconnected
  have hConn : IsPreconnected {s : ℂ | 0 < s.re} := by
    apply Convex.isPreconnected
    intro x (hx : 0 < x.re) y (hy : 0 < y.re) a b ha hb hab
    change 0 < (a • x + b • y).re
    have hax : (a • x).re = a * x.re := by
      simp [Complex.real_smul]
    have hby : (b • y).re = b * y.re := by
      simp [Complex.real_smul]
    rw [Complex.add_re, hax, hby]
    have : a > 0 ∨ b > 0 := by
      by_contra h
      have ha_nonpos : a ≤ 0 := by
        by_contra ha_pos
        exact h (Or.inl (lt_of_not_ge ha_pos))
      have hb_nonpos : b ≤ 0 := by
        by_contra hb_pos
        exact h (Or.inr (lt_of_not_ge hb_pos))
      have ha_zero : a = 0 := le_antisymm ha_nonpos ha
      have hb_zero : b = 0 := le_antisymm hb_nonpos hb
      linarith [hab, ha_zero, hb_zero]
    rcases this with ha' | hb'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.le) (mul_pos hb' hy)
  -- Pick a witness z₀ with Re(z₀) > 1 ⊂ {Re > 0}
  -- z₀ = 2 works: Re(2) = 2 > 0 and Re(2) > 1
  have hz₀ : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  -- F =ᶠ[𝓝 z₀] G because F = G on the open set {Re > 1} ∋ z₀
  have hEv : F =ᶠ[nhds (2 : ℂ)] G := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨{s : ℂ | 1 < s.re}, isOpen_lt continuous_const Complex.continuous_re
      |>.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re), fun s hs => hFG s hs⟩
  -- Apply the identity principle
  have hEqOn : Set.EqOn F G {s | 0 < s.re} :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG hConn hz₀ hEv
  exact fun s hs => hEqOn hs

/--
**Full analytic continuation chain.**
Combines the analytic continuation bridge with Thm 14 (c₀ ≠ 0) to get
`Z_spec = ζ` from analyticity witnesses alone.
-/
theorem routeK_analytic_continuation_Zspec
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ (fun s => Dinf s - Binf s)
      {s | 0 < s.re})
    (hG : AnalyticOnNhd ℂ (fun s => c0Complex s * ζfun s)
      {s | 0 < s.re})
    (hAlg : ∀ s : ℂ, 1 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s) :
    ∀ s : ℂ, 0 < s.re →
      routeK_Zspec Dinf Binf s = ζfun s := by
  have hCont := routeK_analytic_continuation_bridge hF hG hAlg
  exact routeK_continuation_Zspec_eq_zeta hCont

/--
Analytic version of the final off-axis zero-exclusion reduction.
The continuation side is discharged by the existing analytic bridge; the only
remaining endpoint input is off-axis nonvanishing of `Z_spec` itself.
-/
theorem routeK_analytic_global_zero_exclusion_of_Zspec_nonvanishing
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ (fun s => Dinf s - Binf s)
      {s | 0 < s.re})
    (hG : AnalyticOnNhd ℂ (fun s => c0Complex s * ζfun s)
      {s | 0 < s.re})
    (hAlg : ∀ s : ℂ, 1 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hZspec : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  have hCont := routeK_analytic_continuation_bridge hF hG hAlg
  exact routeK_global_zero_exclusion_of_Zspec_nonvanishing hCont hZspec


end LeanC2
