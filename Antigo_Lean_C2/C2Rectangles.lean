import LeanC2.C2ArgumentPrinciple

namespace LeanC2

open scoped BigOperators

/-!
### Rectangle contours for the C2 odd-channel argument certificate

This module gives a concrete finite-contour shape for the abstract
argument-principle hand-off in `C2ArgumentPrinciple.lean`: nondegenerate
axis-aligned rectangles, finite samples certified to lie on their boundary,
and promotion from rectangle shell certificates to the existing C2 odd-channel
shell API.
-/

/-- Nondegenerate axis-aligned rectangle in the complex plane. -/
structure routeK_Rectangle where
  reMin : ℝ
  reMax : ℝ
  imMin : ℝ
  imMax : ℝ
  hRe : reMin < reMax
  hIm : imMin < imMax

/-- Complex point with prescribed real and imaginary coordinates. -/
def routeK_Rectangle.point (x y : ℝ) : ℂ :=
  ⟨x, y⟩

@[simp]
theorem routeK_Rectangle.point_re (x y : ℝ) :
    (routeK_Rectangle.point x y).re = x :=
  rfl

@[simp]
theorem routeK_Rectangle.point_im (x y : ℝ) :
    (routeK_Rectangle.point x y).im = y :=
  rfl

/-- Closed rectangle as a set of complex points. -/
def routeK_Rectangle.closed (R : routeK_Rectangle) : Set ℂ :=
  {z | R.reMin ≤ z.re ∧ z.re ≤ R.reMax ∧ R.imMin ≤ z.im ∧ z.im ≤ R.imMax}

/-- Boundary of the closed rectangle. -/
def routeK_Rectangle.boundary (R : routeK_Rectangle) : Set ℂ :=
  {z |
    ((z.re = R.reMin ∨ z.re = R.reMax) ∧ R.imMin ≤ z.im ∧ z.im ≤ R.imMax) ∨
      ((z.im = R.imMin ∨ z.im = R.imMax) ∧ R.reMin ≤ z.re ∧ z.re ≤ R.reMax)}

theorem routeK_Rectangle.leftPoint_mem_boundary
    (R : routeK_Rectangle) {y : ℝ} (hyMin : R.imMin ≤ y) (hyMax : y ≤ R.imMax) :
    routeK_Rectangle.point R.reMin y ∈ R.boundary := by
  left
  exact ⟨Or.inl rfl, hyMin, hyMax⟩

theorem routeK_Rectangle.rightPoint_mem_boundary
    (R : routeK_Rectangle) {y : ℝ} (hyMin : R.imMin ≤ y) (hyMax : y ≤ R.imMax) :
    routeK_Rectangle.point R.reMax y ∈ R.boundary := by
  left
  exact ⟨Or.inr rfl, hyMin, hyMax⟩

theorem routeK_Rectangle.bottomPoint_mem_boundary
    (R : routeK_Rectangle) {x : ℝ} (hxMin : R.reMin ≤ x) (hxMax : x ≤ R.reMax) :
    routeK_Rectangle.point x R.imMin ∈ R.boundary := by
  right
  exact ⟨Or.inl rfl, hxMin, hxMax⟩

theorem routeK_Rectangle.topPoint_mem_boundary
    (R : routeK_Rectangle) {x : ℝ} (hxMin : R.reMin ≤ x) (hxMax : x ≤ R.reMax) :
    routeK_Rectangle.point x R.imMax ∈ R.boundary := by
  right
  exact ⟨Or.inr rfl, hxMin, hxMax⟩

/-- The four corners of a rectangle as a finite boundary sample. -/
noncomputable def routeK_Rectangle.corners (R : routeK_Rectangle) : Finset ℂ :=
  { routeK_Rectangle.point R.reMin R.imMin,
    routeK_Rectangle.point R.reMax R.imMin,
    routeK_Rectangle.point R.reMax R.imMax,
    routeK_Rectangle.point R.reMin R.imMax }

theorem routeK_Rectangle.corners_subset_boundary (R : routeK_Rectangle) :
    ∀ z ∈ routeK_Rectangle.corners R, z ∈ R.boundary := by
  classical
  intro z hz
  have hz' :
      z = routeK_Rectangle.point R.reMin R.imMin ∨
        z = routeK_Rectangle.point R.reMax R.imMin ∨
        z = routeK_Rectangle.point R.reMax R.imMax ∨
        z = routeK_Rectangle.point R.reMin R.imMax := by
    simpa [routeK_Rectangle.corners] using hz
  rcases hz' with rfl | rfl | rfl | rfl
  · exact routeK_Rectangle.bottomPoint_mem_boundary R
      (x := R.reMin) le_rfl (le_of_lt R.hRe)
  · exact routeK_Rectangle.bottomPoint_mem_boundary R
      (x := R.reMax) (le_of_lt R.hRe) le_rfl
  · exact routeK_Rectangle.topPoint_mem_boundary R
      (x := R.reMax) (le_of_lt R.hRe) le_rfl
  · exact routeK_Rectangle.topPoint_mem_boundary R
      (x := R.reMin) le_rfl (le_of_lt R.hRe)

/-- A finite sample whose points are certified to lie on a rectangle boundary. -/
structure routeK_RectangleBoundarySample (R : routeK_Rectangle) where
  points : Finset ℂ
  onBoundary : ∀ z ∈ points, z ∈ R.boundary

/-- Corner-only finite boundary sample. -/
noncomputable def routeK_Rectangle.cornerSample
    (R : routeK_Rectangle) : routeK_RectangleBoundarySample R where
  points := routeK_Rectangle.corners R
  onBoundary := routeK_Rectangle.corners_subset_boundary R

/--
Turn a certified rectangle boundary sample plus nonvanishing and winding-count
data into the generic argument-principle count certificate.
-/
theorem routeK_RectangleBoundarySample.to_countCertificate
    {R : routeK_Rectangle} (sample : routeK_RectangleBoundarySample R)
    {windingCount zeroCount : ℕ}
    (hNonzero : ∀ z ∈ sample.points, c2OddPrincipalChannel z ≠ 0)
    (hcount : zeroCount = windingCount) :
    routeK_C2ArgumentPrincipleCountCertificate c2OddPrincipalChannel
      R.boundary sample.points windingCount zeroCount := by
  exact ⟨fun z hz => ⟨sample.onBoundary z hz, hNonzero z hz⟩, hcount⟩

/--
Rectangle-specialized shell certificate for the C2 odd channel.

This is the concrete form intended for later numerical or analytic contour
certificates: each dyadic shell comes with a rectangle, a finite boundary
sample on that rectangle, a certified winding count, and the density estimates
needed by the C2 shell API.
-/
def routeK_C2OddRectangleArgumentPrincipleShellCertificateAt
    (s : ℂ) (shells : Finset ℕ)
    (rect : ℕ → routeK_Rectangle)
    (sample : ∀ j : ℕ, routeK_RectangleBoundarySample (rect j))
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
      (∀ z ∈ (sample j).points, c2OddPrincipalChannel z ≠ 0) ∧
      zeroCount j = windingCount j ∧
      0 < shellScale j ∧
      0 ≤ shellContribution j ∧
      shellContribution j ≤ (zeroCount j : ℝ) / shellScale j ∧
      (windingCount j : ℝ) ≤ densityC * shellScale j * ell) ∧
    (shells.card : ℝ) ≤ shellCountC * ell ∧
    base + densityC * shellCountC ≤ C

/-- Rectangle shell certificates produce the generic shell certificates. -/
theorem routeK_C2OddArgumentPrincipleShellCertificateAt_of_rectangle
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_RectangleBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateAt s shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddArgumentPrincipleShellCertificateAt s shells
      (fun j => (rect j).boundary) (fun j => (sample j).points)
      windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C := by
  rcases hcert with
    ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, hShell, hCard, hC⟩
  refine ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, ?_, hCard, hC⟩
  intro j hj
  rcases hShell j hj with
    ⟨hNonzero, hcount, hscale_pos, hcontrib0, hcontrib, hwindDensity⟩
  refine ⟨?_, hscale_pos, hcontrib0, hcontrib, hwindDensity⟩
  exact ⟨fun z hz => ⟨(sample j).onBoundary z hz, hNonzero z hz⟩, hcount⟩

/-- Rectangle shell certificates imply the pointwise C2 odd-channel beta bound. -/
theorem routeK_C2OddChannelBetaBoundAt_of_rectangleArgumentPrincipleShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_RectangleBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateAt s shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundAt s C := by
  exact routeK_C2OddChannelBetaBoundAt_of_argumentPrincipleShellCertificate
    (routeK_C2OddArgumentPrincipleShellCertificateAt_of_rectangle hcert)

/-- Explicit-constant pointwise rectangle certificate variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitAt_of_rectangleArgumentPrincipleShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {rect : ℕ → routeK_Rectangle}
    {sample : ∀ j : ℕ, routeK_RectangleBoundarySample (rect j)}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateAt s shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitAt s := by
  simpa [routeK_C2OddChannelBetaBoundExplicitAt] using
    routeK_C2OddChannelBetaBoundAt_of_rectangleArgumentPrincipleShellCertificate hcert

/-- Global rectangle-specialized shell certificate for the C2 odd channel. -/
def routeK_C2OddRectangleArgumentPrincipleShellCertificateGlobal
    (shells : ℂ → Finset ℕ)
    (rect : ℂ → ℕ → routeK_Rectangle)
    (sample : ∀ s : ℂ, ∀ j : ℕ, routeK_RectangleBoundarySample (rect s j))
    (windingCount zeroCount : ℂ → ℕ → ℕ)
    (shellContribution shellScale : ℂ → ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C2OddRectangleArgumentPrincipleShellCertificateAt s (shells s)
      (rect s) (sample s) (windingCount s) (zeroCount s)
      (shellContribution s) (shellScale s) base densityC shellCountC C

/-- Global rectangle certificates produce the generic global shell certificate. -/
theorem routeK_C2OddArgumentPrincipleShellCertificateGlobal_of_rectangle
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample : ∀ s : ℂ, ∀ j : ℕ, routeK_RectangleBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateGlobal shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddArgumentPrincipleShellCertificateGlobal shells
      (fun s j => (rect s j).boundary) (fun s j => (sample s j).points)
      windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C := by
  intro s hs hstrip hhalf
  exact routeK_C2OddArgumentPrincipleShellCertificateAt_of_rectangle
    (hcert s hs hstrip hhalf)

/-- Global rectangle certificates imply the global C2 odd-channel beta bound. -/
theorem routeK_C2OddChannelBetaBoundGlobal_of_rectangleArgumentPrincipleShellCertificate
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample : ∀ s : ℂ, ∀ j : ℕ, routeK_RectangleBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateGlobal shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundGlobal C := by
  exact routeK_C2OddChannelBetaBoundGlobal_of_argumentPrincipleShellCertificateGlobal
    (routeK_C2OddArgumentPrincipleShellCertificateGlobal_of_rectangle hcert)

/-- Explicit-constant global rectangle certificate variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitGlobal_of_rectangleArgumentPrincipleShellCertificate
    {shells : ℂ → Finset ℕ}
    {rect : ℂ → ℕ → routeK_Rectangle}
    {sample : ∀ s : ℂ, ∀ j : ℕ, routeK_RectangleBoundarySample (rect s j)}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddRectangleArgumentPrincipleShellCertificateGlobal shells rect
      sample windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitGlobal := by
  simpa [routeK_C2OddChannelBetaBoundExplicitGlobal] using
    routeK_C2OddChannelBetaBoundGlobal_of_rectangleArgumentPrincipleShellCertificate hcert

end LeanC2
