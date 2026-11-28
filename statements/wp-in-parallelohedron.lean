import Mathlib

/-!
# Voronoi's conjecture on parallelohedra

Source: https://en.wikipedia.org/wiki/Parallelohedron
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Voronoi's conjecture (open in dimensions `≥ 6`, listed under parallelohedra): every
parallelohedron is an affine image of a Voronoi cell (Dirichlet–Voronoi domain) of a lattice.

## Encoding

* Work in `ℝᵈ = EuclideanSpace ℝ (Fin d)`. A lattice is the `ℤ`-span of a basis `b` of `ℝᵈ`.
* A parallelohedron is a convex polytope (convex hull of a finite set) with nonempty interior
  whose translates by the points of some lattice tile `ℝᵈ`: they cover the space and distinct
  translates have disjoint interiors. (By Venkov–McMullen, a convex polytope tiling `ℝᵈ` by
  translations at all admits such a face-to-face lattice tiling, so this agrees with the usual
  definitions.)
* The Voronoi cell of a lattice `L` is `{x | ∀ v ∈ L, ‖x‖ ≤ ‖x - v‖}`.
* "Affine image" means the image under an affine automorphism of `ℝᵈ`.
-/

namespace OMA.S_wp_in_parallelohedron

/-- The lattice spanned by a basis `b` of `ℝᵈ`. -/
def lattice {d : ℕ} (b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range b)

/-- `P` is a parallelohedron: a full-dimensional convex polytope tiling space by lattice
translates. -/
def IsParallelohedron {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∃ S : Finset (EuclideanSpace ℝ (Fin d)), P = convexHull ℝ (S : Set _)) ∧
    (interior P).Nonempty ∧
    ∃ b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      (∀ x, ∃ v ∈ lattice b, x - v ∈ P) ∧
      ∀ v ∈ lattice b, ∀ w ∈ lattice b, v ≠ w →
        Disjoint ((fun x => v + x) '' interior P) ((fun x => w + x) '' interior P)

/-- The Voronoi cell of the lattice spanned by `b`. -/
def voronoiCell {d : ℕ} (b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ v ∈ lattice b, ‖x‖ ≤ ‖x - v‖}

theorem main :
    ∀ (d : ℕ) (P : Set (EuclideanSpace ℝ (Fin d))), IsParallelohedron P →
      ∃ (A : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
        (b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))),
        A '' P = voronoiCell b := by
  sorry

end OMA.S_wp_in_parallelohedron
