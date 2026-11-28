import Mathlib

/-!
# Once differentiable, piecewise degree three polynomials on triangulated planar domains

Source: https://mathoverflow.net/questions/72189/once-differentiable-piecewise-degree-three-polynomials-on-triangulated-planar-d
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Strang; asked on the page): for every triangulation of a polygonal domain in the
plane, the space `S` of `C¹` functions on the domain that are polynomials of degree at most `3` on
each triangle has dimension exactly `3 V_B + 2 V_I + 1 + σ` (`V_B`, `V_I`: numbers of boundary
and interior vertices; `σ`: number of singular vertices). The lower bound is known.

Conventions:
* A triangulation is a finite family of nondegenerate closed triangles, any two distinct ones
  meeting in nothing, a common vertex, or a common edge. Its domain `D` (the union) is required to
  be a polygonal region: homeomorphic to a closed disc. Vertices and edges are those of the
  triangles; a vertex is interior if it lies in the interior of `D`, a boundary vertex otherwise.
* A singular vertex is an interior vertex lying on exactly four edges, these forming two straight
  lines through it (each neighbour has an opposite neighbour with the vertex strictly between).
* A function in `S` is given by its polynomials `p_T` (degree `≤ 3`) on the triangles `T`; it is
  `C¹` iff any two of them agree, with their gradients, at every common point. This identifies
  `S` with a subspace of the tuples `(p_T)`, whose dimension is taken.
-/

namespace OMA.S_mo_72189

open Classical

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

variable {m : ℕ}

/-- The closed triangle with vertices `t`. -/
def tri (t : Fin 3 → P) : Set P := convexHull ℝ (Set.range t)

/-- A triangulation of a polygonal region by triangles `t i`. -/
def IsTriangulation (t : Fin m → Fin 3 → P) : Prop :=
  (∀ i, AffineIndependent ℝ (t i)) ∧
  (∀ i j, i ≠ j → tri (t i) ∩ tri (t j) = ∅ ∨
      (∃ a b, t i a = t j b ∧ tri (t i) ∩ tri (t j) = {t i a}) ∨
      (∃ a a' b b', a ≠ a' ∧ t i a = t j b ∧ t i a' = t j b' ∧
        tri (t i) ∩ tri (t j) = segment ℝ (t i a) (t i a'))) ∧
  Nonempty ((⋃ i, tri (t i)) ≃ₜ Metric.closedBall (0 : P) 1)

/-- The domain. -/
def dom (t : Fin m → Fin 3 → P) : Set P := ⋃ i, tri (t i)

/-- The vertices. -/
def verts (t : Fin m → Fin 3 → P) : Set P := ⋃ i, Set.range (t i)

/-- `v w` is an edge. -/
def IsEdge (t : Fin m → Fin 3 → P) (v w : P) : Prop :=
  v ≠ w ∧ ∃ i a b, t i a = v ∧ t i b = w

/-- Interior vertices. -/
def interiorVerts (t : Fin m → Fin 3 → P) : Set P := verts t ∩ interior (dom t)

/-- Boundary vertices. -/
def boundaryVerts (t : Fin m → Fin 3 → P) : Set P := verts t \ interior (dom t)

/-- Singular vertices. -/
def singularVerts (t : Fin m → Fin 3 → P) : Set P :=
  {v ∈ interiorVerts t | {w | IsEdge t v w}.ncard = 4 ∧
    ∀ w, IsEdge t v w → ∃ w', IsEdge t v w' ∧ v ∈ openSegment ℝ w w'}

/-- Evaluation of a bivariate polynomial at a point. -/
noncomputable def ev (p : MvPolynomial (Fin 2) ℝ) (x : P) : ℝ := MvPolynomial.eval (fun k => x k) p

/-- The space `S`, as the set of tuples of cubic pieces matching to first order on common points
(a linear subspace; its span is itself). -/
noncomputable def splineSet (t : Fin m → Fin 3 → P) : Set (Fin m → MvPolynomial (Fin 2) ℝ) :=
  {p | (∀ i, (p i).totalDegree ≤ 3) ∧ ∀ i j, ∀ x ∈ tri (t i) ∩ tri (t j),
    ev (p i) x = ev (p j) x ∧ ∀ k, ev (MvPolynomial.pderiv k (p i)) x = ev (MvPolynomial.pderiv k (p j)) x}

theorem main :
    ∀ (m : ℕ) (t : Fin m → Fin 3 → P), IsTriangulation t →
      Module.finrank ℝ (Submodule.span ℝ (splineSet t)) =
        3 * (boundaryVerts t).ncard + 2 * (interiorVerts t).ncard + 1 + (singularVerts t).ncard := by
  sorry

end OMA.S_mo_72189
