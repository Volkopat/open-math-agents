import Mathlib

/-!
# Voronoi's conjecture on parallelohedra

Source: https://en.wikipedia.org/wiki/Voronoi_diagram
Does every higher-dimensional tiling by translations of convex polytope tiles have an affine
transformation taking it to a Voronoi diagram?

Conventions. This is Voronoi's conjecture (1908) in its standard form: every parallelohedron,
i.e. every convex polytope `P ⊆ ℝᵈ` whose translates tile `ℝᵈ` (they cover space and have
pairwise disjoint interiors), is the image under an affine bijection of the Voronoi cell
`{x | ∀ l ∈ L, ‖x‖ ≤ ‖x - l‖}` of some lattice `L` (the `ℤ`-span of a basis of `ℝᵈ`). By
Venkov–McMullen a parallelohedron also tiles face-to-face by lattice translates, and under
the affine map that tiling becomes the Voronoi diagram of `L`; the literal reading for
arbitrary (non-face-to-face) translation tilings already fails for shifted rows of squares.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_voronoi_diagram

open Set

theorem main :
    ∀ (d : ℕ) (F : Finset (EuclideanSpace ℝ (Fin d))),
      let P := convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin d)))
      (interior P).Nonempty →
      (∃ T : Set (EuclideanSpace ℝ (Fin d)),
          (⋃ t ∈ T, (fun x => t + x) '' P) = univ ∧
          ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
            Disjoint (interior ((fun x => t + x) '' P)) (interior ((fun x => t' + x) '' P))) →
      ∃ (A : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
        (b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))),
        A '' P = {x | ∀ l ∈ Submodule.span ℤ (range b), ‖x‖ ≤ ‖x - l‖} := by
  sorry

end OMA.S_wp_voronoi_diagram
