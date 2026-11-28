import Mathlib

/-!
# Edge-antipodal colorings of cubes

Source: https://www.openproblemgarden.org/op/edge_antipodal_colorings_of_cubes
Credit: @ishaanzee

Let `Q_d` denote the `d`-dimensional cube graph. A map `φ : E(Q_d) → {0, 1}` is called
edge-antipodal if `φ(e) ≠ φ(e')` whenever `e, e'` are antipodal edges.

**Conjecture** (S. Norine). If `d ≥ 2` and `φ : E(Q_d) → {0, 1}` is edge-antipodal, then
there exist a pair of antipodal vertices `v, v'` of `Q_d` which are joined by a monochromatic
path.

Formalization:
* The vertices of `Q_d` are the binary words `Fin d → Bool`, two being adjacent when they
  differ in exactly one coordinate.
* The antipode of `v` flips every coordinate; the antipodal edge of `e = {x, y}` is
  `{x', y'}` (`Sym2.map` of the antipode), again an edge of `Q_d`.
* A 2-coloring of the edges is a map `φ : Sym2 (Fin d → Bool) → Bool`; only its values on edges
  matter, and edge-antipodality is required on edges only.
* A monochromatic path from `v` to `v'` is a path in `Q_d` all of whose edges have one color.
-/

namespace OMA.S_opg_edge_antipodal_colorings_of_cubes

/-- The `d`-dimensional cube graph `Q_d`: binary words of length `d`, adjacent when they differ
in exactly one coordinate. -/
def cube (d : ℕ) : SimpleGraph (Fin d → Bool) :=
  SimpleGraph.fromRel fun x y => (Finset.univ.filter fun i => x i ≠ y i).card = 1

/-- The antipodal vertex: every coordinate flipped. -/
def antipode {d : ℕ} (v : Fin d → Bool) : Fin d → Bool := fun i => !v i

/-- `φ` is edge-antipodal: antipodal edges of `Q_d` get different colors. -/
def IsEdgeAntipodal {d : ℕ} (φ : Sym2 (Fin d → Bool) → Bool) : Prop :=
  ∀ e ∈ (cube d).edgeSet, φ (e.map antipode) ≠ φ e

/-- **Norine's conjecture**: for `d ≥ 2`, every edge-antipodal 2-coloring of the edges of
`Q_d` has a monochromatic path joining some pair of antipodal vertices. -/
theorem main : ∀ d : ℕ, 2 ≤ d → ∀ φ : Sym2 (Fin d → Bool) → Bool, IsEdgeAntipodal φ →
    ∃ (v : Fin d → Bool) (p : (cube d).Walk v (antipode v)) (c : Bool),
      p.IsPath ∧ ∀ e ∈ p.edges, φ e = c := by
  sorry

end OMA.S_opg_edge_antipodal_colorings_of_cubes
