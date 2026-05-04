import LeanC2.C2RectangleMesh

namespace LeanC2

open scoped BigOperators

/-!
### Discrete argument increments on ordered boundary meshes

This module records the finite winding hand-off in a form suitable for later
numerical or interval certificates.  A discrete argument certificate consists
of cyclic consecutive argument increments along an ordered boundary list, with
total increment equal to `2π * windingCount`.
-/

/-- The real constant `2π`. -/
noncomputable def routeK_twoPi : ℝ := 2 * Real.pi

/-- Cyclic successor in a nonempty list. -/
def routeK_ListCyclicNext {α : Type*} (points : List α)
    (hpts : 0 < points.length) (i : Fin points.length) : α :=
  points.get ⟨(i.1 + 1) % points.length, Nat.mod_lt _ hpts⟩

/--
Certified discrete argument increment between two consecutive sampled points.

The interval constraint records that the supplied increment is a principal
branch increment; the actual interval/numeric proof can be supplied later by a
certified evaluator.
-/
def routeK_DiscreteArgumentStepCertificate
    (F : ℂ → ℂ) (z w : ℂ) (delta : ℝ) : Prop :=
  F z ≠ 0 ∧ F w ≠ 0 ∧ -Real.pi ≤ delta ∧ delta ≤ Real.pi

/--
Closed-loop discrete argument certificate for an ordered sample.

The `increment` family is indexed by `Fin points.length`, so `increment i`
belongs to the cyclic consecutive pair `(points[i], points[i+1])`.
-/
def routeK_DiscreteArgumentLoopCertificate
    (F : ℂ → ℂ) (points : List ℂ) (windingCount : ℕ) : Prop :=
  ∃ hpts : 0 < points.length,
  ∃ increment : Fin points.length → ℝ,
    (∀ z ∈ points, F z ≠ 0) ∧
    (∀ i : Fin points.length,
      routeK_DiscreteArgumentStepCertificate F (points.get i)
        (routeK_ListCyclicNext points hpts i) (increment i)) ∧
    (∑ i : Fin points.length, increment i) = routeK_twoPi * (windingCount : ℝ)

namespace routeK_Rectangle

/--
An ordered rectangle boundary sample with a discrete argument certificate
produces the generic argument-principle count certificate.
-/
theorem routeK_RectangleOrderedBoundarySample.to_countCertificate_of_discreteArgument
    {R : routeK_Rectangle} (sample : routeK_RectangleOrderedBoundarySample R)
    {windingCount zeroCount : ℕ}
    (hdisc : routeK_DiscreteArgumentLoopCertificate c2OddPrincipalChannel
      sample.points windingCount)
    (hcount : zeroCount = windingCount) :
    routeK_C2ArgumentPrincipleCountCertificate c2OddPrincipalChannel
      R.boundary sample.points.toFinset windingCount zeroCount := by
  rcases hdisc with ⟨_hpts, _increment, hNonzero, _hStep, _hTotal⟩
  exact sample.to_countCertificate hNonzero hcount

end routeK_Rectangle

/--
Shell certificate where each shell count comes from a discrete argument
certificate on an ordered rectangular boundary sample.
-/
def routeK_C2OddDiscreteArgumentShellCertificateAt
    (s : ℂ) (shells : Finset ℕ)
    (rect : ℕ → routeK_Rectangle)
    (sample : ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect j))
    (windingCount zeroCount : ℕ → ℕ)
    (shellContribution shellScale : ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∃ ell : ℝ,
    ell = Real.log (routeK_offAxisHeight s) ∧
    0 ≤ base ∧
    0 ≤ densityC ∧
    0 ≤ shellCountC ∧
    1 ≤ ell ∧
    ‖c2OddPrincipalChannelBeta s‖ ≤
      base * ell + ∑ j ∈ shells, shellContribution j ∧
    (∀ j ∈ shells,
      routeK_DiscreteArgumentLoopCertificate c2OddPrincipalChannel
        (sample j).points (windingCount j) ∧
      zeroCount j = windingCount j ∧
      0 < shellScale j ∧
      0 ≤ shellContribution j ∧
      shellContribution j ≤ (zeroCount j : ℝ) / shellScale j ∧
      (windingCount j : ℝ) ≤ densityC * shellScale j * ell) ∧
    (shells.card : ℝ) ≤ shellCountC * ell ∧
    base + densityC * shellCountC ≤ C

/--
Discrete argument shell certificates produce the abstract
argument-principle shell certificates.
-/
theorem routeK_C2OddArgumentPrincipleShellCertificateAt_of_discreteArgument
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateAt s shells rect sample
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddArgumentPrincipleShellCertificateAt s shells
      (fun j => (rect j).boundary) (fun j => (sample j).points.toFinset)
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C := by
  rcases hcert with
    ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, hShell, hCard, hC⟩
  refine ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, ?_, hCard, hC⟩
  intro j hj
  rcases hShell j hj with
    ⟨hdisc, hcount, hscale_pos, hcontrib0, hcontrib, hwindDensity⟩
  refine ⟨?_, hscale_pos, hcontrib0, hcontrib, hwindDensity⟩
  exact (sample j).to_countCertificate_of_discreteArgument hdisc hcount

/-- Pointwise C2 odd-channel beta bound from discrete argument shell certificates. -/
theorem routeK_C2OddChannelBetaBoundAt_of_discreteArgumentShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateAt s shells rect sample
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundAt s C := by
  exact routeK_C2OddChannelBetaBoundAt_of_argumentPrincipleShellCertificate
    (routeK_C2OddArgumentPrincipleShellCertificateAt_of_discreteArgument hcert)

/-- Explicit-constant pointwise variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitAt_of_discreteArgumentShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateAt s shells rect sample
      windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitAt s := by
  simpa [routeK_C2OddChannelBetaBoundExplicitAt] using
    routeK_C2OddChannelBetaBoundAt_of_discreteArgumentShellCertificate hcert

/-- Global discrete argument shell certificate. -/
def routeK_C2OddDiscreteArgumentShellCertificateGlobal
    (shells : ℂ → Finset ℕ)
    (rect : ℂ → ℕ → routeK_Rectangle)
    (sample :
      ∀ s : ℂ, ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect s j))
    (windingCount zeroCount : ℂ → ℕ → ℕ)
    (shellContribution shellScale : ℂ → ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C2OddDiscreteArgumentShellCertificateAt s (shells s)
      (rect s) (sample s) (windingCount s) (zeroCount s)
      (shellContribution s) (shellScale s) base densityC shellCountC C

/-- Global promotion from discrete argument shells to argument-principle shells. -/
theorem routeK_C2OddArgumentPrincipleShellCertificateGlobal_of_discreteArgument
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample :
      ∀ s : ℂ, ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateGlobal shells rect sample
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddArgumentPrincipleShellCertificateGlobal shells
      (fun s j => (rect s j).boundary) (fun s j => (sample s j).points.toFinset)
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C := by
  intro s hs hstrip hhalf
  exact routeK_C2OddArgumentPrincipleShellCertificateAt_of_discreteArgument
    (hcert s hs hstrip hhalf)

/-- Global C2 odd-channel beta bound from discrete argument shell certificates. -/
theorem routeK_C2OddChannelBetaBoundGlobal_of_discreteArgumentShellCertificate
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample :
      ∀ s : ℂ, ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateGlobal shells rect sample
      windingCount zeroCount shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundGlobal C := by
  exact routeK_C2OddChannelBetaBoundGlobal_of_argumentPrincipleShellCertificateGlobal
    (routeK_C2OddArgumentPrincipleShellCertificateGlobal_of_discreteArgument hcert)

/-- Global explicit-constant variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitGlobal_of_discreteArgumentShellCertificate
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample :
      ∀ s : ℂ, ∀ j : ℕ, routeK_Rectangle.routeK_RectangleOrderedBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddDiscreteArgumentShellCertificateGlobal shells rect sample
      windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitGlobal := by
  simpa [routeK_C2OddChannelBetaBoundExplicitGlobal] using
    routeK_C2OddChannelBetaBoundGlobal_of_discreteArgumentShellCertificate hcert

end LeanC2
