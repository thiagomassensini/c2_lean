import Mathlib
import LeanC2.Identity.C0NonZero
import LeanC2.Operators.BranchToGenuine
import LeanC2.Operators.Genuine

set_option linter.style.whitespace false

namespace LeanC2

open scoped LSeries.notation

/-- Thm 13 packaged as a statement on the half-plane `Re(s) > 1`. -/
def fundamentalIdentityOnRightHalfPlane (zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 1 < s.re → FInfinity s = c0 s * zetaFun s

/--
Right-half-plane factorization of the C2 numerator through the center coefficient and odd side.
-/
def centerFactorizationOnRightHalfPlane : Prop :=
  ∀ s : Complex, 1 < s.re → FInfinity s = centerCoeff s * oddZeta s

/-- Right-half-plane factorization of the odd side through a zeta-like channel. -/
def oddZetaFactorizationOnRightHalfPlane (zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 1 < s.re → oddZeta s = (1 - (2 : Complex) ^ (-s)) * zetaFun s

lemma oddCore_injective : Function.Injective oddCore := by
  intro m n h
  unfold oddCore at h
  omega

lemma mem_range_oddCore_iff (n : Nat) : n ∈ Set.range oddCore ↔ Odd n := by
  constructor
  · rintro ⟨m, rfl⟩
    simp
  · intro hn
    rcases hn with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    unfold oddCore
    omega

lemma trivCharTwo_apply_nat (n : Nat) :
    (1 : DirichletCharacter Complex 2) n = if Odd n then 1 else 0 := by
  by_cases hodd : Odd n
  · have hz : (n : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hodd
    simp [hz, hodd]
  · have heven : Even n := Nat.not_odd_iff_even.mp hodd
    have hz : (n : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr heven
    simpa [hz, hodd] using
      (MulChar.map_nonunit (1 : DirichletCharacter Complex 2) (a := (0 : ZMod 2)) not_isUnit_zero)

/-- The odd-core Dirichlet series is the trivial Dirichlet `L`-function modulo `2`. -/
theorem oddZeta_eq_LFunctionTrivChar_two {s : Complex} (hs : 1 < s.re) :
    oddZeta s = DirichletCharacter.LFunctionTrivChar 2 s := by
  let χ : DirichletCharacter Complex 2 := 1
  let hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hsum :
      HasSum (fun n : Nat => dirichletSummandHom χ hs0 n)
        (DirichletCharacter.LFunctionTrivChar 2 s) := by
    have hsumm : Summable (fun n : Nat => dirichletSummandHom χ hs0 n) :=
      (summable_dirichletSummand χ hs).of_norm
    have htsum :
        (∑' n : Nat, dirichletSummandHom χ hs0 n) =
          DirichletCharacter.LFunctionTrivChar 2 s := by
      calc
        ∑' n : Nat, dirichletSummandHom χ hs0 n = L ↗χ s := by
          simpa [χ, hs0] using (tsum_dirichletSummand χ hs)
        _ = DirichletCharacter.LFunctionTrivChar 2 s := by
          symm
          simpa [χ] using (DirichletCharacter.LFunction_eq_LSeries χ hs)
    rw [← htsum]
    exact hsumm.hasSum
  have hOutside :
      ∀ n : Nat, n ∉ Set.range oddCore → dirichletSummandHom χ hs0 n = 0 := by
    intro n hn
    have hnotodd : ¬ Odd n := by
      intro hodd
      exact hn ((mem_range_oddCore_iff n).2 hodd)
    simp [dirichletSummandHom, trivCharTwo_apply_nat, hnotodd, χ]
  have hsumOdd :
      HasSum (fun m : Nat => dirichletSummandHom χ hs0 (oddCore m))
        (DirichletCharacter.LFunctionTrivChar 2 s) := by
    exact (oddCore_injective.hasSum_iff hOutside).2 hsum
  have hsumCore :
      HasSum (fun m : Nat => (((oddCore m : Nat) : Complex) ^ (-s)))
        (DirichletCharacter.LFunctionTrivChar 2 s) := by
    simpa [dirichletSummandHom, trivCharTwo_apply_nat, χ] using hsumOdd
  simpa [oddZeta] using hsumCore.tsum_eq

/-- The odd channel matches the usual odd Euler factor times the Riemann zeta function. -/
theorem oddZeta_factorization_riemannZeta :
    oddZetaFactorizationOnRightHalfPlane riemannZeta := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hs
  calc
    oddZeta s = DirichletCharacter.LFunctionTrivChar 2 s :=
      oddZeta_eq_LFunctionTrivChar_two hs
    _ = (∏ p ∈ (2 : Nat).primeFactors, (1 - (p : Complex) ^ (-s))) * riemannZeta s := by
      simpa using (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs1)
    _ = (1 - (2 : Complex) ^ (-s)) * riemannZeta s := by
      have hpf : (2 : Nat).primeFactors = {2} := by
        ext p
        simp [Nat.prime_two]
      rw [hpf]
      simp

lemma norm_shellRatio_eq (s : Complex) : ‖shellRatio s‖ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-s.re) := by
  have hcpow : ‖((2 : Complex) ^ (-s))‖ = (2 : ℝ) ^ (-s.re) := by
    simpa using (Complex.norm_natCast_cpow_of_pos (by decide : 0 < 2) (-s))
  rw [shellRatio, norm_mul, norm_div, norm_one]
  norm_num
  rw [hcpow]

lemma norm_shellRatio_lt_one_of_re_gt_neg_one {s : Complex}
  (hs : -1 < s.re) : ‖shellRatio s‖ < 1 := by
  have hexp : -s.re < (1 : ℝ) := by
    linarith
  have hpow : (2 : ℝ) ^ (-s.re) < 2 := by
    simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexp
  rw [norm_shellRatio_eq s]
  nlinarith

lemma norm_shellRatio_lt_one {s : Complex} (hs : 1 < s.re) : ‖shellRatio s‖ < 1 := by
  exact norm_shellRatio_lt_one_of_re_gt_neg_one (by linarith)

/-- The center-only double series factorizes into the shell coefficient times the odd channel. -/
theorem centerSeries_eq_centerCoeff_mul_oddZeta {s : Complex} (hs : 1 < s.re) :
    centerSeries s = centerCoeff s * oddZeta s := by
  let a : Nat -> Complex := fun j => ((2 : Complex) * shellRatio s ^ 2) * shellRatio s ^ j
  let b : Nat -> Complex := fun m => ((((oddCore m : Nat) : Complex) ^ (-s)))
  have hq : ‖shellRatio s‖ < 1 := norm_shellRatio_lt_one hs
  have haNorm : Summable (fun j : Nat => ‖a j‖) := by
    have hbase : Summable (fun j : Nat =>
        ‖(2 : Complex) * shellRatio s ^ 2‖ * ‖shellRatio s ^ j‖) :=
      (summable_norm_geometric_of_norm_lt_one hq).mul_left
        ‖(2 : Complex) * shellRatio s ^ 2‖
    exact hbase.congr fun j => by
      dsimp [a]
      simp [mul_assoc]
  have hbNorm : Summable (fun m : Nat => ‖b m‖) := by
    let χ : DirichletCharacter Complex 2 := 1
    have hbase : Summable (fun m : Nat =>
        ‖dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) (oddCore m)‖) :=
      (summable_dirichletSummand χ hs).comp_injective oddCore_injective
    convert hbase using 1 with m
    dsimp [b]
    simp [dirichletSummandHom, trivCharTwo_apply_nat, χ]
  have hb : Summable b := hbNorm.of_norm
  have hfiber : ∀ j : Nat, Summable (fun m : Nat => a j * b m) := by
    intro j
    exact hb.mul_left (a j)
  have hprod : Summable (Function.uncurry fun j m => a j * b m) := by
    exact summable_mul_of_summable_norm haNorm hbNorm
  have hgeom : Summable (fun j : Nat => shellRatio s ^ j) :=
    summable_geometric_of_norm_lt_one hq
  have htsumA : (∑' j : Nat, a j) = centerCoeff s := by
    calc
      ∑' j : Nat, a j = ((2 : Complex) * shellRatio s ^ 2) * ∑' j : Nat, shellRatio s ^ j := by
        dsimp [a]
        exact (hgeom.hasSum.mul_left ((2 : Complex) * shellRatio s ^ 2)).tsum_eq
      _ = ((2 : Complex) * shellRatio s ^ 2) * Ring.inverse (1 - shellRatio s) := by
        rw [geom_series_eq_inverse _ hq]
      _ = centerCoeff s := by
        unfold centerCoeff
        rw [Ring.inverse_eq_inv']
        simp [div_eq_mul_inv, mul_assoc]
  calc
    centerSeries s = ∑' j : Nat, ∑' m : Nat, a j * b m := by
      unfold centerSeries
      refine tsum_congr ?_
      intro j
      refine tsum_congr ?_
      intro m
      dsimp [a, b]
      calc
        centerTerm s (j + 2) m =
            ((2 : Complex) * shellRatio s ^ (j + 2)) * ((((oddCore m : Nat) : Complex) ^ (-s))) :=
          centerTerm_eq_shellRatio_pow_mul_oddCore s (j + 2) m
        _ = (((2 : Complex) * shellRatio s ^ 2) * shellRatio s ^ j) *
              ((((oddCore m : Nat) : Complex) ^ (-s))) := by
            rw [pow_add]
            ring
        _ = a j * b m := by rfl
    _ = ∑' p : Nat × Nat, a p.1 * b p.2 := by
      symm
      exact hprod.tsum_prod_uncurry hfiber
    _ = (∑' j : Nat, a j) * ∑' m : Nat, b m := by
      symm
      exact tsum_mul_tsum_of_summable_norm haNorm hbNorm
    _ = centerCoeff s * oddZeta s := by
      rw [htsumA]
      simp [b, oddZeta]

lemma summable_norm_oddCore_cpow_neg {s : Complex} (hs : 1 < s.re) :
    Summable (fun m : Nat => ‖(((oddCore m : Nat) : Complex) ^ (-s))‖) := by
  let χ : DirichletCharacter Complex 2 := 1
  have hbase : Summable (fun m : Nat =>
      ‖dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) (oddCore m)‖) :=
    (summable_dirichletSummand χ hs).comp_injective oddCore_injective
  convert hbase using 1 with m
  simp [dirichletSummandHom, trivCharTwo_apply_nat, χ]

lemma summable_norm_const_dyadicWeight_shift (c : Complex) :
    Summable (fun j : Nat => ‖c * dyadicComplexWeight (j + 2)‖) := by
  let r : Complex := (1 : Complex) / 2
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    norm_num
  have hbase : Summable (fun j : Nat => ‖c * r ^ 2‖ * ‖r ^ j‖) :=
    (summable_norm_geometric_of_norm_lt_one hr).mul_left ‖c * r ^ 2‖
  exact hbase.congr fun j => by
    dsimp [r, dyadicComplexWeight]
    rw [pow_add, norm_mul, norm_mul, norm_mul]
    ring

lemma four_le_two_pow_shift (j : Nat) : 4 <= 2 ^ (j + 2) := by
  calc
    4 = 2 ^ 2 := by norm_num
    _ <= 2 ^ (j + 2) := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

lemma norm_natCast_cpow_neg_antitone {s : Complex} (hs : 1 < s.re) {a b : Nat}
    (ha : 0 < a) (hab : a <= b) :
    ‖(((b : Nat) : Complex) ^ (-s))‖ <= ‖(((a : Nat) : Complex) ^ (-s))‖ := by
  have hbNorm : ‖(((b : Nat) : Complex) ^ (-s))‖ = (b : Real) ^ (-s.re) := by
    simpa using
      (Complex.norm_natCast_cpow_of_re_ne_zero b (s := -s)
        (Complex.re_neg_ne_zero_of_one_lt_re hs))
  have haNorm : ‖(((a : Nat) : Complex) ^ (-s))‖ = (a : Real) ^ (-s.re) := by
    simpa using
      (Complex.norm_natCast_cpow_of_re_ne_zero a (s := -s)
        (Complex.re_neg_ne_zero_of_one_lt_re hs))
  rw [hbNorm, haNorm]
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast ha)
    (by exact_mod_cast hab)
    (by linarith)

lemma oddCore_le_natDescendant_shift (j m : Nat) (epsilon : BranchSign) :
    oddCore m <= natDescendant (j + 2) epsilon (oddCore m) := by
  cases epsilon
  · have hpow : 4 <= 2 ^ (j + 2) := four_le_two_pow_shift j
    have hcore : oddCore m + 1 <= centerNat (j + 2) m := by
      have hmul : 4 * oddCore m <= 2 ^ (j + 2) * oddCore m := Nat.mul_le_mul_right _ hpow
      have hsmall : oddCore m + 1 <= 4 * oddCore m := by
        unfold oddCore
        omega
      exact hsmall.trans (by simpa [centerNat, Nat.mul_comm] using hmul)
    have : oddCore m <= centerNat (j + 2) m - 1 := by omega
    simpa [natDescendant, centerNat]
  · have hpow : 4 <= 2 ^ (j + 2) := four_le_two_pow_shift j
    have hmul : 4 * oddCore m <= 2 ^ (j + 2) * oddCore m := Nat.mul_le_mul_right _ hpow
    have hsmall : oddCore m <= 4 * oddCore m := by
      have hpos : 0 < oddCore m := oddCore_pos m
      omega
    have hcore : oddCore m <= centerNat (j + 2) m :=
      hsmall.trans (by simpa [centerNat, Nat.mul_comm] using hmul)
    have : oddCore m <= centerNat (j + 2) m + 1 := le_trans hcore (Nat.le_succ _)
    simpa [natDescendant, centerNat] using this

lemma oddCore_le_centerNat_shift (j m : Nat) : oddCore m <= centerNat (j + 2) m := by
  have hpow : 4 <= 2 ^ (j + 2) := four_le_two_pow_shift j
  have hmul : 4 * oddCore m <= 2 ^ (j + 2) * oddCore m := Nat.mul_le_mul_right _ hpow
  have hsmall : oddCore m <= 4 * oddCore m := by
    have hpos : 0 < oddCore m := oddCore_pos m
    omega
  exact hsmall.trans (by simpa [centerNat, Nat.mul_comm] using hmul)

lemma norm_centerTerm_shift_le {s : Complex} (hs : 1 < s.re) (j m : Nat) :
    ‖centerTerm s (j + 2) m‖ <=
      ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
        ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
  have hcenter := norm_natCast_cpow_neg_antitone hs
    (oddCore_pos m) (oddCore_le_centerNat_shift j m)
  unfold centerTerm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hcenter (norm_nonneg _)

lemma norm_legPairTerm_shift_le {s : Complex} (hs : 1 < s.re) (j m : Nat) :
    ‖legPairTerm s (j + 2) m‖ <=
      ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
        ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
  have hminus := norm_natCast_cpow_neg_antitone hs
    (oddCore_pos m) (oddCore_le_natDescendant_shift j m BranchSign.minus)
  have hplus := norm_natCast_cpow_neg_antitone hs
    (oddCore_pos m) (oddCore_le_natDescendant_shift j m BranchSign.plus)
  unfold legPairTerm legTerm
  calc
    ‖dyadicComplexWeight (j + 2) *
          ((((natDescendant (j + 2) BranchSign.minus (oddCore m) : Nat) : Complex) ^ (-s))) +
        dyadicComplexWeight (j + 2) *
          ((((natDescendant (j + 2) BranchSign.plus (oddCore m) : Nat) : Complex) ^ (-s)))‖
        <=
          ‖dyadicComplexWeight (j + 2) *
              ((((natDescendant (j + 2) BranchSign.minus (oddCore m) : Nat) : Complex) ^ (-s)))‖ +
            ‖dyadicComplexWeight (j + 2) *
              ((((natDescendant (j + 2) BranchSign.plus (oddCore m) : Nat) : Complex) ^ (-s)))‖ :=
      norm_add_le _ _
    _ = ‖dyadicComplexWeight (j + 2)‖ *
          ‖((((natDescendant (j + 2) BranchSign.minus (oddCore m) : Nat) : Complex) ^ (-s)))‖ +
        ‖dyadicComplexWeight (j + 2)‖ *
          ‖((((natDescendant (j + 2) BranchSign.plus (oddCore m) : Nat) : Complex) ^ (-s)))‖ := by
      rw [norm_mul, norm_mul]
    _ <= ‖dyadicComplexWeight (j + 2)‖ * ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ +
          ‖dyadicComplexWeight (j + 2)‖ * ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hminus (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hplus (norm_nonneg _))
    _ = (2 * ‖dyadicComplexWeight (j + 2)‖) * ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
      ring
    _ = ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
          ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
      rw [norm_mul, Complex.norm_two]

lemma norm_bracketTerm_shift_le {s : Complex} (hs : 1 < s.re) (j m : Nat) :
    ‖bracketTerm s (j + 2) m‖ <=
      (2 * ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖) *
        ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
  have hleg := norm_legPairTerm_shift_le hs j m
  have hcenter := norm_centerTerm_shift_le hs j m
  have hEq : bracketTerm s (j + 2) m = legPairTerm s (j + 2) m - centerTerm s (j + 2) m := by
    calc
      bracketTerm s (j + 2) m =
          bracketTerm s (j + 2) m + centerTerm s (j + 2) m - centerTerm s (j + 2) m := by
        ring
      _ = legPairTerm s (j + 2) m - centerTerm s (j + 2) m := by
        rw [← legPair_eq_bracket_add_centerTerm]
  calc
    ‖bracketTerm s (j + 2) m‖ = ‖legPairTerm s (j + 2) m - centerTerm s (j + 2) m‖ := by
      rw [hEq]
    _ <= ‖legPairTerm s (j + 2) m‖ + ‖centerTerm s (j + 2) m‖ := by
      simpa [sub_eq_add_neg] using
        norm_add_le (legPairTerm s (j + 2) m) (-centerTerm s (j + 2) m)
    _ <=
          ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
              ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ +
            ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
              ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ :=
      add_le_add hleg hcenter
    _ = (2 * ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖) *
          ‖(((oddCore m : Nat) : Complex) ^ (-s))‖ := by
      ring

-- Exact infinite cancellation on the convergent half-plane.
set_option maxHeartbeats 800000 in
-- The double-tsum reindexing and termwise cancellation elaborate slowly but terminate.
theorem FInfinity_eq_centerSeries_on_right_half_plane {s : Complex} (hs : 1 < s.re) :
    FInfinity s = centerSeries s := by
  let f : Nat × Nat -> Complex := fun p => legPairTerm s (p.1 + 2) p.2
  let g : Nat × Nat -> Complex := fun p => bracketTerm s (p.1 + 2) p.2
  let h : Nat × Nat -> Complex := fun p => centerTerm s (p.1 + 2) p.2
  let coeff2 : Nat -> Real := fun j => ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖
  let coeff4 : Nat -> Real := fun j => 2 * coeff2 j
  let oddNorm : Nat -> Real := fun m => ‖(((oddCore m : Nat) : Complex) ^ (-s))‖
  have hcoeff2 : Summable coeff2 := by
    simpa [coeff2] using summable_norm_const_dyadicWeight_shift (2 : Complex)
  have hcoeff4 : Summable coeff4 := by
    simpa [coeff4] using hcoeff2.mul_left (2 : Real)
  have hodd : Summable oddNorm := by
    simpa [oddNorm] using summable_norm_oddCore_cpow_neg hs
  have hcoeff2Nonneg : ∀ j : Nat, 0 <= coeff2 j := by
    intro j
    dsimp [coeff2]
    exact norm_nonneg _
  have hcoeff4Nonneg : ∀ j : Nat, 0 <= coeff4 j := by
    intro j
    dsimp [coeff4]
    nlinarith [hcoeff2Nonneg j]
  have hoddNonneg : ∀ m : Nat, 0 <= oddNorm m := by
    intro m
    dsimp [oddNorm]
    exact norm_nonneg _
  have hmaj2 : Summable (fun p : Nat × Nat => coeff2 p.1 * oddNorm p.2) := by
    exact hcoeff2.mul_of_nonneg hodd hcoeff2Nonneg hoddNonneg
  have hmaj4 : Summable (fun p : Nat × Nat => coeff4 p.1 * oddNorm p.2) := by
    exact hcoeff4.mul_of_nonneg hodd hcoeff4Nonneg hoddNonneg
  have hfNorm : Summable (fun p : Nat × Nat => ‖f p‖) := by
    refine hmaj2.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    rintro ⟨j, m⟩
    simpa [f, coeff2, oddNorm] using norm_legPairTerm_shift_le hs j m
  have hgNorm : Summable (fun p : Nat × Nat => ‖g p‖) := by
    refine hmaj4.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    rintro ⟨j, m⟩
    simpa [g, coeff4, coeff2, oddNorm, norm_mul, Complex.norm_two, mul_assoc, mul_left_comm,
      mul_comm] using norm_bracketTerm_shift_le hs j m
  have hhNorm : Summable (fun p : Nat × Nat => ‖h p‖) := by
    refine hmaj2.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    rintro ⟨j, m⟩
    simpa [h, coeff2, oddNorm] using norm_centerTerm_shift_le hs j m
  have hf : Summable f := hfNorm.of_norm
  have hg : Summable g := hgNorm.of_norm
  have hh : Summable h := hhNorm.of_norm
  have hfiber : ∀ j : Nat, Summable (fun m : Nat => f (j, m)) := fun j => hf.prod_factor j
  have hgfiber : ∀ j : Nat, Summable (fun m : Nat => g (j, m)) := fun j => hg.prod_factor j
  have hhfiber : ∀ j : Nat, Summable (fun m : Nat => h (j, m)) := fun j => hh.prod_factor j
  have hD : ∑' p : Nat × Nat, f p = DInfinity s := by
    calc
      ∑' p : Nat × Nat, f p = ∑' j : Nat, ∑' m : Nat, f (j, m) :=
        hf.tsum_prod_uncurry hfiber
      _ = DInfinity s := by
        simp [DInfinity, f]
  have hB : ∑' p : Nat × Nat, g p = BInfinity s := by
    calc
      ∑' p : Nat × Nat, g p = ∑' j : Nat, ∑' m : Nat, g (j, m) :=
        hg.tsum_prod_uncurry hgfiber
      _ = BInfinity s := by
        simp [BInfinity, g]
  have hC : ∑' p : Nat × Nat, h p = centerSeries s := by
    calc
      ∑' p : Nat × Nat, h p = ∑' j : Nat, ∑' m : Nat, h (j, m) :=
        hh.tsum_prod_uncurry hhfiber
      _ = centerSeries s := by
        simp [centerSeries, h]
  calc
    FInfinity s = DInfinity s - BInfinity s := by
      simp [FInfinity]
    _ = (∑' p : Nat × Nat, f p) - ∑' p : Nat × Nat, g p := by
      rw [hD, hB]
    _ = ∑' p : Nat × Nat, (f p - g p) := by
      symm
      exact hf.tsum_sub hg
    _ = ∑' p : Nat × Nat, h p := by
      refine tsum_congr ?_
      rintro ⟨j, m⟩
      simpa [f, g, h] using legPair_sub_bracket_eq_centerTerm s (j + 2) m
    _ = centerSeries s := hC

/-- Right-half-plane factorization of `F∞` through `centerCoeff * oddZeta`. -/
theorem centerFactorization_on_right_half_plane : centerFactorizationOnRightHalfPlane := by
  intro s hs
  calc
    FInfinity s = centerSeries s := FInfinity_eq_centerSeries_on_right_half_plane hs
    _ = centerCoeff s * oddZeta s := centerSeries_eq_centerCoeff_mul_oddZeta hs

lemma shellRatio_eq_inv_two_mul_twoCpow (s : Complex) :
    shellRatio s = (((2 : Complex) * ((2 : Complex) ^ s))⁻¹) := by
  have hpow0 : ((2 : Complex) ^ s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
  unfold shellRatio
  rw [Complex.cpow_neg]
  field_simp [hpow0]

lemma twoCpow_neg_two_mul (s : Complex) :
    (2 : Complex) ^ (-2 * s) = (((2 : Complex) ^ s)⁻¹) ^ (2 : Nat) := by
  calc
    (2 : Complex) ^ (-2 * s) = (2 : Complex) ^ (-s * 2) := by ring_nf
    _ = ((2 : Complex) ^ (-s)) ^ (2 : Nat) := by
      simpa using (Complex.cpow_mul_nat (2 : Complex) (-s) 2)
    _ = (((2 : Complex) ^ s)⁻¹) ^ (2 : Nat) := by rw [Complex.cpow_neg]

/-- The shell coefficient times the odd/even correction factor is exactly `c0`. -/
theorem centerCoeff_mul_oddFactor_eq_c0 (s : Complex) :
    centerCoeff s * (1 - (2 : Complex) ^ (-s)) = c0 s := by
  let u : Complex := (2 : Complex) ^ s
  have hu0 : u ≠ 0 := by
    dsimp [u]
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
  have hshell : shellRatio s = ((2 : Complex) * u)⁻¹ := by
    simpa [u] using shellRatio_eq_inv_two_mul_twoCpow s
  have hpow : (2 : Complex) ^ (-2 * s) = (u⁻¹) ^ (2 : Nat) := by
    simpa [u] using twoCpow_neg_two_mul s
  unfold centerCoeff c0
  rw [hshell, hpow, Complex.cpow_neg]
  field_simp [hu0]
  ring

/-- Once the center factorization and odd-zeta factorization are established, Thm 13 follows. -/
theorem fundamentalIdentity_of_factorizations {zetaFun : Complex -> Complex}
    (hCenter : centerFactorizationOnRightHalfPlane)
    (hOdd : oddZetaFactorizationOnRightHalfPlane zetaFun) :
    fundamentalIdentityOnRightHalfPlane zetaFun := by
  intro s hs
  calc
    FInfinity s = centerCoeff s * oddZeta s := hCenter s hs
    _ = centerCoeff s * ((1 - (2 : Complex) ^ (-s)) * zetaFun s) := by rw [hOdd s hs]
    _ = (centerCoeff s * (1 - (2 : Complex) ^ (-s))) * zetaFun s := by ring
    _ = c0 s * zetaFun s := by rw [centerCoeff_mul_oddFactor_eq_c0]

/-- Once the center channel is identified, the odd side already specializes to `riemannZeta`. -/
theorem fundamentalIdentity_of_centerFactorization
    (hCenter : centerFactorizationOnRightHalfPlane) :
    fundamentalIdentityOnRightHalfPlane riemannZeta := by
  exact fundamentalIdentity_of_factorizations hCenter oddZeta_factorization_riemannZeta

/-- Concrete Thm 13 on `Re(s) > 1` with the Riemann zeta channel. -/
theorem fundamentalIdentity_riemannZeta_on_right_half_plane :
    fundamentalIdentityOnRightHalfPlane riemannZeta := by
  exact fundamentalIdentity_of_centerFactorization centerFactorization_on_right_half_plane

/-- Backward-compatible alias for the Thm 13 model statement. -/
abbrev routeK_thm13_model (zetaFun : Complex -> Complex) : Prop :=
  fundamentalIdentityOnRightHalfPlane zetaFun

theorem routeK_thm13_model_iff (zetaFun : Complex -> Complex) :
    routeK_thm13_model zetaFun ↔ fundamentalIdentityOnRightHalfPlane zetaFun := by
  rfl

/-- Pointwise ratio form of Thm 13 on the convergent side `Re(s) > 1`. -/
theorem fundamentalIdentity_ratio_of_model {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {s : Complex} (hs : 1 < s.re) :
    FInfinity s / c0 s = zetaFun s := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos (by linarith)
  calc
    FInfinity s / c0 s = (c0 s * zetaFun s) / c0 s := by simp [hId s hs]
    _ = zetaFun s := by field_simp [hc0]

/-- Thm 13 transfers nonvanishing between the numerator and the zeta channel. -/
theorem fundamentalIdentity_nonzero_iff {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {s : Complex} (hs : 1 < s.re) :
    FInfinity s ≠ 0 ↔ zetaFun s ≠ 0 := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos (by linarith)
  constructor
  · intro hF hz
    apply hF
    rw [hId s hs, hz, mul_zero]
  · intro hz hF
    rw [hId s hs] at hF
    exact hz ((mul_eq_zero.mp hF).resolve_left hc0)

/-- Off-axis evaluation form of the ratio statement, still on the side `σ > 1`. -/
theorem routeK_thm13_ratio_offaxis {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) /
        c0 ((sigma : Complex) + t * Complex.I) =
      zetaFun ((sigma : Complex) + t * Complex.I) := by
  simpa using
    (fundamentalIdentity_ratio_of_model hId
      (s := ((sigma : Complex) + t * Complex.I))
      (by simpa using hsigma))

/-- Right-half-plane nonvanishing transfer from `F∞` to the zeta channel. -/
theorem routeK_thm13_nonzero_transfer {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) ≠ 0 ↔
      zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  simpa using
    (fundamentalIdentity_nonzero_iff hId
      (s := ((sigma : Complex) + t * Complex.I))
      (by simpa using hsigma))

/-!
Usable Thm 13 interface: once the identity `F_infty = c0 * zeta` is established on
`Re(s) > 1`, this file exposes the ratio and nonvanishing consequences needed by the
later transfer layers.

Primary sources:
- docs/algebra_Z_igual_zeta.md
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Identity.lean
-/

end LeanC2