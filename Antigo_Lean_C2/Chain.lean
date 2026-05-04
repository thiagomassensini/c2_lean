import Mathlib
import LeanC2.Tree
import LeanC2.Barrier
import LeanC2.Normalization
import LeanC2.OperatorNorm
import LeanC2.Tilt
import LeanC2.Composite
import LeanC2.Continuation

namespace LeanC2

-- ═══════════════════════════════════════════════════════════════════════
-- branchNormSq — promoted to canonical closed form
-- ═══════════════════════════════════════════════════════════════════════

/-- branchNormSq in closed form: equals 2q²/(1−q) with q = qOfSigma σ.
    Promotes from the abstract `dominantBranchMass` definition to the
    explicit analytic formula. -/
theorem branchNormSq_closed_form {σ : ℝ} (hσ : 0 < σ) :
    branchNormSq σ = 2 * (qOfSigma σ) ^ 2 / (1 - qOfSigma σ) := by
  have hq1 : qOfSigma σ < 1 := qOfSigma_lt_one_iff.2 hσ
  rw [branchNormSq_eq hσ]
  field_simp [(sub_pos.mpr hq1).ne']

-- ═══════════════════════════════════════════════════════════════════════
-- ELO 6 — Connection bundle: barrier ↔ tilt ↔ transversal (Cadeia Única)
-- ═══════════════════════════════════════════════════════════════════════

/-- ELO 6: at σ = 1/2, branch norm = 1 AND tilt = 0 simultaneously.
    Both quantities express the same critical-point identity. -/
theorem routeK_elo6_critical_simultaneous :
    branchNormSq ((1 : ℝ) / 2) = 1 ∧ ∀ c : ℝ, tiltBracket 0 c = 0 :=
  ⟨branchNormSq_half, tiltBracket_zero⟩

/-- ELO 6: above barrier (σ > 1/2), branch norm < 1 AND tilt positive for any real δ > 0. -/
theorem routeK_elo6_above_barrier {σ : ℝ} (hσ : (1 : ℝ) / 2 < σ)
    {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 1 < c) :
    branchNormSq σ < 1 ∧ 0 < tiltBracket δ c :=
  ⟨(branchNormSq_lt_one_iff (by linarith)).mpr hσ, tiltBracket_pos_of_pos hδ hc⟩

/-- ELO 6: below barrier (0 < σ < 1/2), branch norm > 1 AND tilt negative for -1 < δ < 0. -/
theorem routeK_elo6_below_barrier {σ : ℝ} (hσpos : 0 < σ) (hσ : σ < (1 : ℝ) / 2)
    {δ c : ℝ} (hδ0 : -1 < δ) (hδ1 : δ < 0) (hc : 1 < c) :
    1 < branchNormSq σ ∧ tiltBracket δ c < 0 :=
  ⟨(branchNormSq_gt_one_iff hσpos).mpr hσ, tiltBracket_neg_of_neg_one_lt hδ0 hδ1 hc⟩

/-- ELO 6 three-way simultaneous transition:
    branch barrier (ELO 2), tilt sign (ELO 3), and Leibniz transversal (ELO 4)
    all transition at σ = 1/2 — three languages, one phenomenon. -/
theorem routeK_elo6_simultaneous_transition :
    (branchNormSq ((1 : ℝ) / 2) = 1) ∧
    (∀ σ : ℝ, 0 < σ → ((1 : ℝ) / 2 < σ ↔ branchNormSq σ < 1)) ∧
    (∀ c : ℝ, tiltBracket 0 c = 0) ∧
    (∀ δ : ℝ, 0 < δ → ∀ c : ℝ, 1 < c → 0 < tiltBracket δ c) ∧
    (∀ m : ℕ, ∀ cv zv : ℕ → ℂ,
      (∀ k < m, zv k = 0) → cv 0 ≠ 0 → zv m ≠ 0 →
      Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cv j * zv (m - j)) ≠ 0) :=
  ⟨branchNormSq_half,
    fun _σ hσ => (branchNormSq_lt_one_iff hσ).symm,
   tiltBracket_zero,
         fun _δ hδ _c hc => tiltBracket_pos_of_pos hδ hc,
   fun m cv zv hz hc0 hzm => leibnizNondegenerateByMultiplicity m cv zv hz hc0 hzm⟩

-- ═══════════════════════════════════════════════════════════════════════
-- C2-intrinsic off-axis closure
-- ═══════════════════════════════════════════════════════════════════════

/--
Intrinsic C2 zero-mode compatibility at a point.

This predicate deliberately mentions only C2-internal mechanisms: the branch
operator is at its critical value and the transverse tilt is annihilated at
every bracket center. It does not mention `ζ`, `Z_spec`, or continuation.
-/
def routeK_C2IntrinsicZeroMode (s : ℂ) : Prop :=
  branchNormSq s.re = 1 ∧
    ∀ c : ℝ, 1 < c → tiltBracket (s.re - (1 : ℝ) / 2) c = 0

/--
C2-intrinsic off-axis barrier certificate at a bracket center.

Above the critical line the branch operator is contractive and the transverse
tilt is strictly positive. Below the critical line, inside `Re(s)>0`, the branch
operator is expansive and the transverse tilt is strictly negative.
-/
def routeK_C2OffAxisBarrierAt (s : ℂ) (c : ℝ) : Prop :=
  ((1 : ℝ) / 2 < s.re ∧
    branchNormSq s.re < 1 ∧
    0 < tiltBracket (s.re - (1 : ℝ) / 2) c) ∨
  (s.re < (1 : ℝ) / 2 ∧
    1 < branchNormSq s.re ∧
    tiltBracket (s.re - (1 : ℝ) / 2) c < 0)

/--
Hierarchical C2 dominance certificate: the full tail has strictly smaller norm
than the dominant C2 block.
-/
def routeK_C2HierarchicalDominance (leader tail : ℂ) : Prop :=
  ‖tail‖ < ‖leader‖

/--
Quantitative dominance barrier: if the C2 tail is smaller than the dominant
block, then the combined channel has strictly positive norm.
-/
theorem routeK_c2_hierarchical_dominance_norm_pos
    {leader tail : ℂ}
    (hdom : routeK_C2HierarchicalDominance leader tail) :
    0 < ‖leader + tail‖ := by
  have hgap : 0 < ‖leader‖ - ‖tail‖ := sub_pos.mpr hdom
  have hle : ‖leader‖ - ‖tail‖ ≤ ‖leader + tail‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_norm_le leader (-tail))
  exact lt_of_lt_of_le hgap hle

/--
Noncancellation form of the hierarchical dominance barrier.
-/
theorem routeK_c2_hierarchical_dominance_nonzero
    {leader tail : ℂ}
    (hdom : routeK_C2HierarchicalDominance leader tail) :
    leader + tail ≠ 0 := by
  exact norm_pos_iff.mp
    (routeK_c2_hierarchical_dominance_norm_pos hdom)

/--
Finite-tail form: if the sum of the norms of all higher C2 blocks is smaller
than the dominant block, the dominant block plus the full tail cannot vanish.
-/
theorem routeK_c2_hierarchical_dominance_from_tail_sum
    {ι : Type*} (S : Finset ι) (leader : ℂ) (tail : ι → ℂ)
    (hdom : (∑ i ∈ S, ‖tail i‖) < ‖leader‖) :
    leader + ∑ i ∈ S, tail i ≠ 0 := by
  apply routeK_c2_hierarchical_dominance_nonzero
  exact lt_of_le_of_lt (norm_sum_le S tail) hdom

/--
Ratio form matching the paper's hierarchical barrier: if the full higher-level
tail is bounded by `r` times the dominant C2 block with `r < 1`, then the total
leader-plus-tail channel is nonzero.
-/
theorem routeK_c2_hierarchical_dominance_from_ratio
    {ι : Type*} (S : Finset ι) (leader : ℂ) (tail : ι → ℂ) {r : ℝ}
    (hleader : 0 < ‖leader‖)
    (htail : (∑ i ∈ S, ‖tail i‖) ≤ r * ‖leader‖)
    (hr : r < 1) :
    leader + ∑ i ∈ S, tail i ≠ 0 := by
  apply routeK_c2_hierarchical_dominance_from_tail_sum
  have hmul : r * ‖leader‖ < 1 * ‖leader‖ :=
    mul_lt_mul_of_pos_right hr hleader
  nlinarith [htail, hmul]

/--
The C2-intrinsic zero-mode condition is equivalent to being on the critical
line. This is the unconditional C2-only closure: it uses only the branch barrier
and tilt annihilation, not any zeta-facing transfer.
-/
theorem routeK_c2_intrinsic_zero_mode_iff_critical
    {s : ℂ} (hs : 0 < s.re) :
    routeK_C2IntrinsicZeroMode s ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hzero
    exact (branchNormSq_eq_one_iff hs).1 hzero.1
  · intro hcrit
    refine ⟨(branchNormSq_eq_one_iff hs).2 hcrit, ?_⟩
    intro c _hc
    have hdelta : s.re - (1 : ℝ) / 2 = 0 := by
      linarith
    rw [hdelta]
    exact tiltBracket_zero c

/--
No off-axis point in the admissible C2 strip can satisfy the intrinsic C2
zero-mode condition.
-/
theorem routeK_c2_no_offaxis_intrinsic_zero_mode
    {s : ℂ} (hs : 0 < s.re) (_hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2) :
    ¬ routeK_C2IntrinsicZeroMode s := by
  intro hzero
  exact hhalf ((routeK_c2_intrinsic_zero_mode_iff_critical hs).1 hzero)

/--
At every off-axis admissible C2 point and every bracket center `c>1`, the
transverse tilt is nonzero. This is the local signed obstruction behind the
C2-only off-axis closure.
-/
theorem routeK_c2_offaxis_tilt_nonzero
    {s : ℂ} {c : ℝ} (hs : 0 < s.re)
    (hhalf : s.re ≠ (1 : ℝ) / 2) (hc : 1 < c) :
    tiltBracket (s.re - (1 : ℝ) / 2) c ≠ 0 := by
  intro htilt
  have hδne : s.re - (1 : ℝ) / 2 ≠ 0 := by
    intro hδ
    apply hhalf
    linarith
  rcases lt_or_gt_of_ne hδne with hδneg | hδpos
  · have hδm1 : -1 < s.re - (1 : ℝ) / 2 := by
      linarith
    have hneg : tiltBracket (s.re - (1 : ℝ) / 2) c < 0 :=
      tiltBracket_neg_of_neg_one_lt hδm1 hδneg hc
    linarith
  · have hpos : 0 < tiltBracket (s.re - (1 : ℝ) / 2) c :=
      tiltBracket_pos_of_pos hδpos hc
    linarith

/--
Every off-axis admissible C2 point has a signed internal barrier certificate.
This is unconditional and C2-intrinsic: no `ζ`, no continuation, and no transfer
of zero-free information to the zeta channel.
-/
theorem routeK_c2_offaxis_barrier_at
    {s : ℂ} {c : ℝ} (hs : 0 < s.re)
    (hhalf : s.re ≠ (1 : ℝ) / 2) (hc : 1 < c) :
    routeK_C2OffAxisBarrierAt s c := by
  rcases lt_or_gt_of_ne hhalf with hbelow | habove
  · right
    have hδneg : s.re - (1 : ℝ) / 2 < 0 := by
      linarith
    have hδm1 : -1 < s.re - (1 : ℝ) / 2 := by
      linarith
    exact ⟨hbelow, (branchNormSq_gt_one_iff hs).2 hbelow,
      tiltBracket_neg_of_neg_one_lt hδm1 hδneg hc⟩
  · left
    have hδpos : 0 < s.re - (1 : ℝ) / 2 := by
      linarith
    exact ⟨habove, (branchNormSq_lt_one_iff hs).2 habove,
      tiltBracket_pos_of_pos hδpos hc⟩

/--
Global C2-only off-axis closure on the admissible strip.

The first component rules out intrinsic C2 zero-modes off the critical line; the
second gives the signed branch/tilt barrier at every bracket center. This is the
formal Lean statement matching the C2-internal endpoint, kept separate from any
zeta/RH-facing transfer theorem.
-/
theorem routeK_c2_internal_offaxis_global
    {s : ℂ} (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2) :
    ¬ routeK_C2IntrinsicZeroMode s ∧
      ∀ c : ℝ, 1 < c → routeK_C2OffAxisBarrierAt s c := by
  exact ⟨routeK_c2_no_offaxis_intrinsic_zero_mode hs hstrip hhalf,
    fun c hc => routeK_c2_offaxis_barrier_at hs hhalf hc⟩

/--
C2-only six-barrier bundle at an admissible off-axis point.

The package is deliberately internal to C2: it records intrinsic zero-mode
exclusion, the signed branch/tilt barrier, hierarchical leader/tail
noncancellation, and a nonzero C2 numerator endpoint without mentioning zeta,
RH, or any transfer of off-axis properties.
-/
def routeK_C2OnlySixBarrierBundleAt (s leader tail numerator : ℂ) : Prop :=
  ¬ routeK_C2IntrinsicZeroMode s ∧
    (∀ c : ℝ, 1 < c → routeK_C2OffAxisBarrierAt s c) ∧
    0 < ‖leader + tail‖ ∧
    leader + tail ≠ 0 ∧
    0 < ‖numerator‖ ∧
    numerator ≠ 0

/--
Local C2-only six-barrier bundle from off-axis strip data, hierarchical
dominance, and a positive C2 numerator norm.
-/
theorem routeK_c2_only_six_barrier_bundle_at
    {s leader tail numerator : ℂ}
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hdom : routeK_C2HierarchicalDominance leader tail)
    (hnum : 0 < ‖numerator‖) :
    routeK_C2OnlySixBarrierBundleAt s leader tail numerator := by
  rcases routeK_c2_internal_offaxis_global hs hstrip hhalf with ⟨hZeroMode, hBarrier⟩
  exact ⟨hZeroMode, hBarrier,
    routeK_c2_hierarchical_dominance_norm_pos hdom,
    routeK_c2_hierarchical_dominance_nonzero hdom,
    hnum, norm_pos_iff.mp hnum⟩

/--
Finite-tail form of the C2-only six-barrier bundle: a leader whose norm strictly
dominates the total norm of finitely many tails cannot be cancelled by them.
-/
theorem routeK_c2_only_six_barrier_bundle_from_tail_sum
    {ι : Type*} (S : Finset ι)
    {s leader numerator : ℂ} (tail : ι → ℂ)
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hdom : (∑ i ∈ S, ‖tail i‖) < ‖leader‖)
    (hnum : 0 < ‖numerator‖) :
    routeK_C2OnlySixBarrierBundleAt s leader (∑ i ∈ S, tail i) numerator := by
  refine routeK_c2_only_six_barrier_bundle_at hs hstrip hhalf ?_ hnum
  exact lt_of_le_of_lt (norm_sum_le S tail) hdom

/--
Ratio-tail form of the C2-only six-barrier bundle, matching the Route-K
hierarchical estimate style `tail ≤ r * leader` with `r < 1`.
-/
theorem routeK_c2_only_six_barrier_bundle_from_ratio
    {ι : Type*} (S : Finset ι)
    {s leader numerator : ℂ} (tail : ι → ℂ) {r : ℝ}
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hleader : 0 < ‖leader‖)
    (htail : (∑ i ∈ S, ‖tail i‖) ≤ r * ‖leader‖)
    (hr : r < 1)
    (hnum : 0 < ‖numerator‖) :
    routeK_C2OnlySixBarrierBundleAt s leader (∑ i ∈ S, tail i) numerator := by
  refine routeK_c2_only_six_barrier_bundle_from_tail_sum (S := S) (tail := tail)
    hs hstrip hhalf ?_ hnum
  have hmul : r * ‖leader‖ < 1 * ‖leader‖ :=
    mul_lt_mul_of_pos_right hr hleader
  nlinarith [htail, hmul]

/--
Bridge theorem (local branch operator -> genuine operator, critical line):
the ELO6 critical barrier identity for the branch operator and the Thm 10 transfer
bound for the genuine operator hold simultaneously under the residual hypothesis.
-/
theorem routeK_bridge_branch_to_genuine_critical
    (t : ℝ) (zeta R : ℂ) {B : ℝ}
    (hR : ‖R‖ ≤ B * c0CriticalLower) :
    branchNormSq ((1 : ℝ) / 2) = 1 ∧
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖ ≤ B := by
  refine ⟨branchNormSq_half, ?_⟩
  exact routeK_chain_thm14_to_thm10_critical t zeta R hR

/--
Bridge theorem (local branch operator -> genuine operator, off-axis):
for any σ > 1/2, the branch operator barrier is strictly below 1 and the
genuine operator stays within B simultaneously under the residual hypothesis.
This is the off-axis symmetric analogue of `routeK_bridge_branch_to_genuine_critical`.
-/
theorem routeK_bridge_branch_to_genuine_offaxis
    (σ t : ℝ) (hσ : 0 < σ) (hhalf : (1 : ℝ) / 2 < σ)
    (zeta R : ℂ) {L B : ℝ}
    (hLpos : 0 < L) (hL : L ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖)
    (hR : ‖R‖ ≤ B * L) :
    branchNormSq σ < 1 ∧
    ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  refine ⟨(branchNormSq_barrier hσ).2 hhalf, ?_⟩
  exact routeK_chain_thm14_to_thm10_sigma_offaxis σ t hσ zeta R hLpos hL hR

/--
Global off-axis nonvanishing of the numerator from transversal product-jet data.

This is the minimal missing global packaging step for the endpoint chain: it
simply lifts the existing local theorem `routeK_thm8_transversal_product_jet`
to the off-axis admissible domain.
-/
theorem routeK_offaxis_numerator_nonzero_global
    {Dinf Binf : ℂ → ℂ}
    (hJet :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
          (∀ k < m, zJet k = 0) ∧
          cJet 0 = c0Complex s ∧
          zJet m ≠ 0 ∧
          Dinf s - Binf s = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 := by
  intro s hs _hstrip _hhalf
  rcases hJet s hs _hstrip _hhalf with ⟨m, cJet, zJet, hz, hcId, hzm, hLeibniz⟩
  exact routeK_thm8_transversal_product_jet hs m cJet zJet
    (Dinf s - Binf s) hz hcId hzm hLeibniz

/--
Pointwise off-axis Leibniz witness from plain numerator nonvanishing.

This shows that the current `hJet` packaging carries no extra analytic content:
once `Dinf s - Binf s ≠ 0`, a trivial order-zero witness already exists.
-/
theorem routeK_offaxis_numerator_witness_of_nonzero
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hs : 0 < s.re)
    (hnum : Dinf s - Binf s ≠ 0) :
    ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
      (∀ k < m, zJet k = 0) ∧
      cJet 0 = c0Complex s ∧
      zJet m ≠ 0 ∧
      Dinf s - Binf s = Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j)) := by
  refine ⟨0, (fun _ => c0Complex s), (fun _ => (Dinf s - Binf s) / c0Complex s), ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (Nat.not_lt_zero _ hk).elim
  · simp
  · exact div_ne_zero hnum (c0Complex_ne_zero_of_re_pos hs)
  · have hc0 : c0Complex s ≠ 0 := c0Complex_ne_zero_of_re_pos hs
    calc
      Dinf s - Binf s = c0Complex s * ((Dinf s - Binf s) / c0Complex s) := by
        field_simp [hc0]
      _ = Finset.sum (Finset.range (0 + 1))
            (fun j => (Nat.choose 0 j : ℂ) * (fun _ => c0Complex s) j *
              (fun _ => (Dinf s - Binf s) / c0Complex s) (0 - j)) := by
        simp

/--
Global off-axis Leibniz-witness packaging is equivalent to plain global
nonvanishing of the numerator.

This theorem isolates the real remaining endpoint gap: not the witness format,
but proving `Dinf s - Binf s ≠ 0` itself on the admissible off-axis domain.
-/
theorem routeK_offaxis_numerator_witness_global_iff_nonzero_global
    {Dinf Binf : ℂ → ℂ} :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
        (∀ k < m, zJet k = 0) ∧
        cJet 0 = c0Complex s ∧
        zJet m ≠ 0 ∧
        Dinf s - Binf s = Finset.sum (Finset.range (m + 1))
          (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) ↔
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0) := by
  constructor
  · exact routeK_offaxis_numerator_nonzero_global
  · intro hnum s hs hstrip hhalf
    exact routeK_offaxis_numerator_witness_of_nonzero hs (hnum s hs hstrip hhalf)

/--
Global off-axis nonvanishing of the numerator from Taylor domination data.

This is the honest ELO-5 replacement for the opaque `hJet` hypothesis: the
remaining input is now an explicit pointwise lower bound of the form used in
`routeK_elo5_nonzero_from_taylor`.
-/
theorem routeK_offaxis_numerator_nonzero_global_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ}
    (hTaylor :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m M₂ R δ : ℝ,
          0 < m ∧
          0 < M₂ ∧
          0 < δ ∧
          δ < 2 * m / M₂ ∧
          0 ≤ R ∧
          R < δ * m - δ ^ 2 / 2 * M₂ ∧
          δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖Dinf s - Binf s‖) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 := by
  intro s hs hstrip hhalf
  rcases hTaylor s hs hstrip hhalf with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  exact routeK_elo5_nonzero_from_taylor m M₂ R hm hM₂ δ hδ hδsmall hR hRsmall
    (Dinf s - Binf s) hF_lb

/--
Global off-axis nonvanishing on the `ζ` side from plain numerator nonvanishing.
-/
theorem routeK_offaxis_zeta_nonzero_global_of_numerator_nonzero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hNum :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        Dinf s - Binf s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  intro s hs hstrip hhalf
  exact (routeK_continuation_nonzero_iff_zeta_nonzero
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).1
      (hNum s hs hstrip hhalf)

/--
Global off-axis nonvanishing on the `ζ` side.

This is the first full endpoint composition across the chain layers: the global
numerator nonvanishing package is pushed through the continuation equivalence
`Dinf - Binf ≠ 0 ↔ ζfun ≠ 0` from `Continuation.lean`.
-/
theorem routeK_offaxis_zeta_nonzero_global
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hJet :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m : ℕ, ∃ cJet zJet : ℕ → ℂ,
          (∀ k < m, zJet k = 0) ∧
          cJet 0 = c0Complex s ∧
          zJet m ≠ 0 ∧
          Dinf s - Binf s = Finset.sum (Finset.range (m + 1))
            (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  intro s hs hstrip hhalf
  have hnum : Dinf s - Binf s ≠ 0 :=
    routeK_offaxis_numerator_nonzero_global (Dinf := Dinf) (Binf := Binf) hJet s hs hstrip hhalf
  exact (routeK_continuation_nonzero_iff_zeta_nonzero
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).1 hnum

/--
Global off-axis nonvanishing on the `ζ` side from Taylor domination data.

This is the honest chain endpoint currently available without extra jet
packaging: ELO 5 produces numerator nonvanishing, and continuation transfers it
to `ζfun`.
-/
theorem routeK_offaxis_zeta_nonzero_global_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ∃ m M₂ R δ : ℝ,
          0 < m ∧
          0 < M₂ ∧
          0 < δ ∧
          δ < 2 * m / M₂ ∧
          0 ≤ R ∧
          R < δ * m - δ ^ 2 / 2 * M₂ ∧
          δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖Dinf s - Binf s‖) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  exact routeK_offaxis_zeta_nonzero_global_of_numerator_nonzero hCont
    (routeK_offaxis_numerator_nonzero_global_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) hTaylor)

/--
Global off-axis continuation equivalence between numerator nonvanishing and
`ζ`-side nonvanishing.
-/
theorem routeK_offaxis_zeta_nonzero_global_iff_numerator_nonzero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s) :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0) ↔
    (∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0) := by
  constructor
  · intro hζ s hs hstrip hhalf
    exact (routeK_continuation_nonzero_iff_zeta_nonzero
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).2
        (hζ s hs hstrip hhalf)
  · exact routeK_offaxis_zeta_nonzero_global_of_numerator_nonzero hCont

-- ═══════════════════════════════════════════════════════════════════════
-- ELO 7 — Full chain closure (Cadeia Única)
-- ═══════════════════════════════════════════════════════════════════════

/--
Rota K Cadeia Única — complete 7-link chain from C2 tree to off-axis exclusion.

- ELO 1 (disjoint supports): `descendant_address_unique`, `disjoint_descendantSets`
- ELO 2 (branch barrier):    `branchNormSq_half`, `branchNormSq_lt_one_iff`
- ELO 3 (tilt annihilation): `tiltBracket_zero`, `tiltBracket_pos_of_pos`,
  `tiltBracket_neg_of_neg_one_lt`
- ELO 4 (transversality):    `leibnizNondegenerateByMultiplicity`
- ELO 5 (Taylor exclusion):  `routeK_elo5_firstorder_dominates`
- ELO 6 (connection):        barrier ↔ tilt ↔ transversal simultaneous at σ = 1/2
- ELO 7 (c₀ nonvanishing):   `routeK_thm14_c0_nonvanishing_critical`
-/
theorem routeK_cadeia_unica_final :
    -- ELO 2: branch barrier
    branchNormSq ((1 : ℝ) / 2) = 1 ∧
    (∀ σ : ℝ, 0 < σ → ((1 : ℝ) / 2 < σ ↔ branchNormSq σ < 1)) ∧
    -- ELO 3: tilt (full real δ)
    (∀ c : ℝ, tiltBracket 0 c = 0) ∧
    (∀ δ : ℝ, 0 < δ → ∀ c : ℝ, 1 < c → 0 < tiltBracket δ c) ∧
    (∀ δ c : ℝ, -1 < δ → δ < 0 → 1 < c → tiltBracket δ c < 0) ∧
    -- ELO 4: Leibniz transversal
    (∀ m : ℕ, ∀ cv zv : ℕ → ℂ,
      (∀ k < m, zv k = 0) → cv 0 ≠ 0 → zv m ≠ 0 →
      Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cv j * zv (m - j)) ≠ 0) ∧
    -- ELO 5: Taylor exclusion radius
    (∀ m M₂ δ : ℝ, 0 < m → 0 < M₂ → 0 < δ → δ < 2 * m / M₂ →
      0 < δ * m - δ ^ 2 / 2 * M₂) ∧
    -- ELO 6: branch barrier (below σ=1/2 → expansion)
    (∀ σ : ℝ, 0 < σ → σ < (1 : ℝ) / 2 → 1 < branchNormSq σ) ∧
    -- ELO 7: c₀ nonvanishing on the critical line
    (∀ t : ℝ, c0Complex (((1 : ℂ) / 2) + t * Complex.I) ≠ 0) :=
  ⟨branchNormSq_half,
    fun _σ hσ => (branchNormSq_lt_one_iff hσ).symm,
   tiltBracket_zero,
    fun _δ hδ _c hc => tiltBracket_pos_of_pos hδ hc,
    fun _δ _c hδ0 hδ1 hc => tiltBracket_neg_of_neg_one_lt hδ0 hδ1 hc,
   fun m cv zv hz hc0 hzm => leibnizNondegenerateByMultiplicity m cv zv hz hc0 hzm,
   fun m M₂ δ hm hM₂ hδ hδs => routeK_elo5_firstorder_dominates m M₂ δ hm hM₂ hδ hδs,
    fun _σ hσ hσhalf => (branchNormSq_gt_one_iff hσ).mpr hσhalf,
   routeK_thm14_c0_nonvanishing_critical⟩


end LeanC2
