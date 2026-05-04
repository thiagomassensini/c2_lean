import Mathlib
import LeanC2.Identity.C0NonZero

namespace LeanC2

/-- Order-`m` Leibniz jet for a product with coefficient jets `c` and `z`. -/
noncomputable def leibnizJet (m : Nat) (c z : Nat -> Complex) : Complex :=
  Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : Complex) * c j * z (m - j))

/--
Literal Leibniz collapse at order `m`: if the `z`-jet vanishes through order `m - 1`,
only the `j = 0` term survives in the product jet.
-/
theorem leibnizCollapseByMultiplicity (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0) :
    leibnizJet m c z = c 0 * z m := by
  unfold leibnizJet
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
Non-degeneracy of the order-`m` product jet once `z` has multiplicity `m` and `c 0` is nonzero.
-/
theorem leibnizNondegenerateByMultiplicity (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  rw [leibnizCollapseByMultiplicity m c z hz]
  exact mul_ne_zero hc0 hzm

/-- Abstract Thm 8 wrapper: multiplicity collapse yields transversal non-degeneracy. -/
theorem transversalJet_nonzero_of_multiplicity (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  exact leibnizNondegenerateByMultiplicity m c z hz hc0 hzm

/-- Rota K abstract form of Thm 8. -/
theorem routeK_thm8_transversal_abstract (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  exact transversalJet_nonzero_of_multiplicity m c z hz hc0 hzm

/--
Rota K chain `Thm 14 -> Thm 8`: identifying the zeroth coefficient with `c0(s)` transfers
the `c0` nonvanishing theorem into transversal non-degeneracy.
-/
theorem routeK_chain_thm14_to_thm8_abstract {s : Complex} (hs : 0 < s.re)
    (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0) (hcId : c 0 = c0 s) (hzm : z m ≠ 0) :
  leibnizJet m c z ≠ 0 := by
  have hc0s : c0 s ≠ 0 := routeK_thm14_c0_nonvanishing_halfplane hs
  have hc0 : c 0 ≠ 0 := by
    intro hc
    apply hc0s
    simpa [hcId] using hc
  exact routeK_thm8_transversal_abstract m c z hz hc0 hzm

/-- Critical-line specialization of `routeK_chain_thm14_to_thm8_abstract`. -/
theorem routeK_chain_thm14_to_thm8_critical (t : Real)
    (m : Nat) (c z : Nat -> Complex)
    (hz : ∀ k < m, z k = 0)
    (hcId : c 0 = c0 (((1 : Complex) / 2) + t * Complex.I))
    (hzm : z m ≠ 0) :
    leibnizJet m c z ≠ 0 := by
  have hs : 0 < ((((1 : Complex) / 2) + t * Complex.I)).re := by
    simp
  exact routeK_chain_thm14_to_thm8_abstract hs m c z hz hcId hzm

/--
Concrete jet bridge for Thm 8: if `Fjet` is identified with the order-`m` Leibniz jet of
`c0 * zeta`, then the jet is nonzero under the multiplicity hypotheses.
-/
theorem routeK_thm8_transversal_product_jet {s : Complex} (hs : 0 < s.re)
    (m : Nat) (cJet zJet : Nat -> Complex) (Fjet : Complex)
    (hz : ∀ k < m, zJet k = 0)
    (hcId : cJet 0 = c0 s)
    (hzm : zJet m ≠ 0)
    (hLeibniz : Fjet = leibnizJet m cJet zJet) :
    Fjet ≠ 0 := by
  intro hF0
  have hsum0 : leibnizJet m cJet zJet = 0 := by
    simpa [hLeibniz] using hF0
  have hsumNe : leibnizJet m cJet zJet ≠ 0 :=
    routeK_chain_thm14_to_thm8_abstract hs m cJet zJet hz hcId hzm
  exact hsumNe hsum0

/-- Critical-line specialization of `routeK_thm8_transversal_product_jet`. -/
theorem routeK_thm8_transversal_product_jet_critical (t : Real)
    (m : Nat) (cJet zJet : Nat -> Complex) (Fjet : Complex)
    (hz : ∀ k < m, zJet k = 0)
    (hcId : cJet 0 = c0 (((1 : Complex) / 2) + t * Complex.I))
    (hzm : zJet m ≠ 0)
    (hLeibniz : Fjet = leibnizJet m cJet zJet) :
    Fjet ≠ 0 := by
  have hs : 0 < ((((1 : Complex) / 2) + t * Complex.I)).re := by
    simp
  exact routeK_thm8_transversal_product_jet hs m cJet zJet Fjet hz hcId hzm hLeibniz

/-!
Scaffold for Thm 8: unconditional transversality near a zeta zero.

Primary sources:
- docs/c2_prova_thm8_transversal.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Tilt.lean
- Lean/Antigo_Lean_C2/Continuation.lean

This module keeps the transversality layer at the jet level: the analytic identification of the
jets remains external, while the Leibniz collapse and the `c0` nonvanishing transfer are fully
formalized here.
-/

end LeanC2
