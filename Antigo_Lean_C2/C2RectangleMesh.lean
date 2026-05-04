import LeanC2.C2Rectangles

namespace LeanC2

open scoped BigOperators

/-!
### Ordered finite meshes on rectangle boundaries

This module prepares the next computational hand-off: boundary samples with an
order around the rectangle.  The winding calculation will eventually use the
list order, while the existing certificates consume finite sets; both views are
provided here.
-/

/-- A finite real mesh certified to lie in the unit interval `[0, 1]`. -/
structure routeK_UnitMesh where
  points : List ℝ
  inUnit : ∀ θ ∈ points, 0 ≤ θ ∧ θ ≤ 1

/-- The endpoint mesh `[0, 1]`. -/
def routeK_UnitMesh.endpoints : routeK_UnitMesh where
  points := [0, 1]
  inUnit := by
    intro θ hθ
    have hθ' : θ = 0 ∨ θ = 1 := by
      simpa using hθ
    rcases hθ' with rfl | rfl
    · constructor <;> norm_num
    · constructor <;> norm_num

/-- Affine interpolation from `a` to `b` using `θ`. -/
def routeK_Rectangle.affineCoord (a b θ : ℝ) : ℝ :=
  (1 - θ) * a + θ * b

theorem routeK_Rectangle.affineCoord_mem_interval
    {a b θ : ℝ} (hab : a ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    a ≤ routeK_Rectangle.affineCoord a b θ ∧
      routeK_Rectangle.affineCoord a b θ ≤ b := by
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hrepr : routeK_Rectangle.affineCoord a b θ = a + θ * (b - a) := by
    unfold routeK_Rectangle.affineCoord
    ring
  have hlower : 0 ≤ θ * (b - a) := mul_nonneg hθ0 hd
  have hupper : θ * (b - a) ≤ b - a := by
    calc
      θ * (b - a) ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right hθ1 hd
      _ = b - a := one_mul _
  constructor
  · rw [hrepr]
    linarith
  · rw [hrepr]
    linarith

theorem routeK_Rectangle.one_sub_mem_unit {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ 1 - θ ∧ 1 - θ ≤ 1 := by
  constructor <;> linarith

namespace routeK_Rectangle

/-- Ordered mesh on the lower horizontal side, traversed left-to-right. -/
def bottomSideMesh (R : routeK_Rectangle) (mesh : routeK_UnitMesh) : List ℂ :=
  mesh.points.map fun θ => point (affineCoord R.reMin R.reMax θ) R.imMin

/-- Ordered mesh on the right vertical side, traversed bottom-to-top. -/
def rightSideMesh (R : routeK_Rectangle) (mesh : routeK_UnitMesh) : List ℂ :=
  mesh.points.map fun θ => point R.reMax (affineCoord R.imMin R.imMax θ)

/-- Ordered mesh on the upper horizontal side, traversed right-to-left. -/
def topSideMesh (R : routeK_Rectangle) (mesh : routeK_UnitMesh) : List ℂ :=
  mesh.points.map fun θ => point (affineCoord R.reMin R.reMax (1 - θ)) R.imMax

/-- Ordered mesh on the left vertical side, traversed top-to-bottom. -/
def leftSideMesh (R : routeK_Rectangle) (mesh : routeK_UnitMesh) : List ℂ :=
  mesh.points.map fun θ => point R.reMin (affineCoord R.imMin R.imMax (1 - θ))

theorem bottomSideMesh_mem_boundary (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    ∀ z ∈ bottomSideMesh R mesh, z ∈ R.boundary := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨θ, hθmem, rfl⟩
  have hθ := mesh.inUnit θ hθmem
  have hx := affineCoord_mem_interval (a := R.reMin) (b := R.reMax)
    (θ := θ) (le_of_lt R.hRe) hθ.1 hθ.2
  exact bottomPoint_mem_boundary R hx.1 hx.2

theorem rightSideMesh_mem_boundary (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    ∀ z ∈ rightSideMesh R mesh, z ∈ R.boundary := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨θ, hθmem, rfl⟩
  have hθ := mesh.inUnit θ hθmem
  have hy := affineCoord_mem_interval (a := R.imMin) (b := R.imMax)
    (θ := θ) (le_of_lt R.hIm) hθ.1 hθ.2
  exact rightPoint_mem_boundary R hy.1 hy.2

theorem topSideMesh_mem_boundary (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    ∀ z ∈ topSideMesh R mesh, z ∈ R.boundary := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨θ, hθmem, rfl⟩
  have hθ := mesh.inUnit θ hθmem
  have hθrev := one_sub_mem_unit hθ.1 hθ.2
  have hx := affineCoord_mem_interval (a := R.reMin) (b := R.reMax)
    (θ := 1 - θ) (le_of_lt R.hRe) hθrev.1 hθrev.2
  exact topPoint_mem_boundary R hx.1 hx.2

theorem leftSideMesh_mem_boundary (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    ∀ z ∈ leftSideMesh R mesh, z ∈ R.boundary := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨θ, hθmem, rfl⟩
  have hθ := mesh.inUnit θ hθmem
  have hθrev := one_sub_mem_unit hθ.1 hθ.2
  have hy := affineCoord_mem_interval (a := R.imMin) (b := R.imMax)
    (θ := 1 - θ) (le_of_lt R.hIm) hθrev.1 hθrev.2
  exact leftPoint_mem_boundary R hy.1 hy.2

/--
Counterclockwise ordered boundary mesh:
bottom side, right side, top side, then left side.
-/
def boundaryMeshLoop (R : routeK_Rectangle) (mesh : routeK_UnitMesh) : List ℂ :=
  bottomSideMesh R mesh ++ rightSideMesh R mesh ++ topSideMesh R mesh ++ leftSideMesh R mesh

theorem boundaryMeshLoop_mem_boundary (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    ∀ z ∈ boundaryMeshLoop R mesh, z ∈ R.boundary := by
  intro z hz
  have hz' :
      z ∈ bottomSideMesh R mesh ∨ z ∈ rightSideMesh R mesh ∨
        z ∈ topSideMesh R mesh ∨ z ∈ leftSideMesh R mesh := by
    simpa [boundaryMeshLoop, or_assoc] using hz
  rcases hz' with h | h | h | h
  · exact bottomSideMesh_mem_boundary R mesh z h
  · exact rightSideMesh_mem_boundary R mesh z h
  · exact topSideMesh_mem_boundary R mesh z h
  · exact leftSideMesh_mem_boundary R mesh z h

/-- Ordered finite boundary sample. -/
structure routeK_RectangleOrderedBoundarySample (R : routeK_Rectangle) where
  points : List ℂ
  onBoundary : ∀ z ∈ points, z ∈ R.boundary

/-- Ordered boundary sample obtained from a certified unit mesh. -/
def orderedBoundaryMeshSample
    (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    routeK_RectangleOrderedBoundarySample R where
  points := boundaryMeshLoop R mesh
  onBoundary := boundaryMeshLoop_mem_boundary R mesh

/-- Convert an ordered boundary sample to the unordered finite sample API. -/
noncomputable def routeK_RectangleOrderedBoundarySample.toBoundarySample
    {R : routeK_Rectangle}
    (sample : routeK_RectangleOrderedBoundarySample R) :
    routeK_RectangleBoundarySample R where
  points := sample.points.toFinset
  onBoundary := by
    intro z hz
    have hzList : z ∈ sample.points := by
      simpa using hz
    exact sample.onBoundary z hzList

/--
Ordered boundary sample plus nonvanishing and winding-count data produces the
generic argument-principle count certificate.
-/
theorem routeK_RectangleOrderedBoundarySample.to_countCertificate
    {R : routeK_Rectangle} (sample : routeK_RectangleOrderedBoundarySample R)
    {windingCount zeroCount : ℕ}
    (hNonzero : ∀ z ∈ sample.points, c2OddPrincipalChannel z ≠ 0)
    (hcount : zeroCount = windingCount) :
    routeK_C2ArgumentPrincipleCountCertificate c2OddPrincipalChannel
      R.boundary sample.points.toFinset windingCount zeroCount := by
  exact (sample.toBoundarySample).to_countCertificate
    (by
      intro z hz
      have hzList : z ∈ sample.points := List.mem_toFinset.mp hz
      exact hNonzero z hzList)
    hcount

/-- Unordered boundary sample obtained from a certified unit mesh. -/
noncomputable def boundaryMeshSample
    (R : routeK_Rectangle) (mesh : routeK_UnitMesh) :
    routeK_RectangleBoundarySample R :=
  (orderedBoundaryMeshSample R mesh).toBoundarySample

end routeK_Rectangle

end LeanC2
