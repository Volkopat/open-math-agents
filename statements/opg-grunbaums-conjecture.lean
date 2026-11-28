import Mathlib

/-!
# Grünbaum's Conjecture

Source: https://www.openproblemgarden.org/op/grunbaums_conjecture
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Grünbaum): if `G` is a simple loopless triangulation of an orientable surface, then
the dual of `G` is `3`-edge-colourable.

## Encoding

* Embedded graphs on closed orientable surfaces are encoded combinatorially as (connected)
  combinatorial maps: a finite set `D` of darts with a fixed-point-free involution `α` (the two
  darts of an edge) and a permutation `σ` (rotation of darts around their vertex). Vertices are
  the cycles of `σ`, edges the orbits of `α`, faces the cycles of `φ = σ * α`. Connectedness of
  the surface: `σ` and `α` generate a group acting transitively on `D`.
* Triangulation: every face has exactly three darts (`φ³ = 1` and `φ` has no fixed point).
* Loopless: the two darts of an edge lie at different vertices. Simple: two darts at the same
  vertex whose partners also share a vertex are equal (no parallel edges).
* The dual graph has the faces as vertices and one edge per edge of `G`; it is cubic. A proper
  `3`-edge-colouring of the dual is a colouring `c : D → Fin 3` constant on edges
  (`c (α x) = c x`) such that the three edges `x, φ x, φ² x` around each face get distinct colours.
-/

namespace OMA.S_opg_grunbaums_conjecture

open Equiv

theorem main :
    ∀ (D : Type) [Fintype D] [DecidableEq D] (σ α : Perm D),
      -- `α` is a fixed-point-free involution
      (∀ x, α (α x) = x) → (∀ x, α x ≠ x) →
      -- connected surface
      (∀ x y, ∃ g ∈ Subgroup.closure ({σ, α} : Set (Perm D)), g x = y) →
      -- every face is a triangle
      (∀ x, (σ * α) ((σ * α) ((σ * α) x)) = x) → (∀ x, (σ * α) x ≠ x) →
      -- loopless
      (∀ x, ¬ σ.SameCycle x (α x)) →
      -- no parallel edges
      (∀ x y, σ.SameCycle x y → σ.SameCycle (α x) (α y) → x = y) →
      ∃ c : D → Fin 3, (∀ x, c (α x) = c x) ∧
        ∀ x, c x ≠ c ((σ * α) x) ∧ c ((σ * α) x) ≠ c ((σ * α) ((σ * α) x)) ∧
          c x ≠ c ((σ * α) ((σ * α) x)) := by
  sorry

end OMA.S_opg_grunbaums_conjecture
