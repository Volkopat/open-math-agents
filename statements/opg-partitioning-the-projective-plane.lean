import Mathlib

/-!
# Partitioning the projective plane

Source: https://www.openproblemgarden.org/op/partitioning_the_projective_plane
Credit: @lzvxck

The source: by projective plane we mean the set of all lines through the origin in `ℝ³`. A
subset `S` of the projective plane is octahedral if all lines in `S` pass through the closure
of two opposite faces of a regular octahedron centered at the origin. `S` is weakly octahedral
if every set `S' ⊆ S` with `|S'| = 3` is octahedral. Conjecture: suppose that the projective
plane can be partitioned into four sets `S₁, S₂, S₃, S₄` such that each `S_i` is weakly
octahedral. Then each `S_i` is octahedral.

Conventions: the projective plane is Mathlib's `Projectivization ℝ (EuclideanSpace ℝ (Fin 3))`,
and a line `p` is spanned by its representative `p.rep`. A regular octahedron centered at the
origin has vertices `± a b₁, ± a b₂, ± a b₃` for an orthonormal basis `b` and some `a > 0`; its
faces are the triangles with vertices `s₁ a b₁, s₂ a b₂, s₃ a b₃` for signs `sᵢ = ±1`, the face
opposite to it having the signs `-sᵢ`. A line spanned by `v ≠ 0` meets the closure of that face
or of the opposite one exactly when the numbers `sᵢ ⟪bᵢ, v⟫` are all `≥ 0` or all `≤ 0`.
Replacing `bᵢ` by `sᵢ bᵢ` (still an orthonormal basis), octahedral therefore means: for some
orthonormal basis `b`, every line in `S` is spanned by a vector whose coordinates in `b` are
all `≥ 0` or all `≤ 0` (a condition that does not depend on the spanning vector chosen).
-/

namespace OMA.S_opg_partitioning_the_projective_plane

/-- `S` is octahedral: for some orthonormal basis `b` of `ℝ³`, each line in `S` has the
coordinates of its spanning vector all of one sign (weakly). -/
def IsOctahedral (S : Set (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) : Prop :=
  ∃ b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)), ∀ p ∈ S,
    (∀ i, 0 ≤ inner ℝ (b i) p.rep) ∨ (∀ i, inner ℝ (b i) p.rep ≤ 0)

/-- `S` is weakly octahedral: every three-element subset of `S` is octahedral. -/
def IsWeaklyOctahedral (S : Set (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) : Prop :=
  ∀ T ⊆ S, T.ncard = 3 → IsOctahedral T

/-- **Partitioning the projective plane (Noel).** If the projective plane is partitioned into
four weakly octahedral sets, then each of them is octahedral. -/
theorem main : ∀ S : Fin 4 → Set (Projectivization ℝ (EuclideanSpace ℝ (Fin 3))),
    (Pairwise fun i j => Disjoint (S i) (S j)) → (⋃ i, S i) = Set.univ →
      (∀ i, IsWeaklyOctahedral (S i)) → ∀ i, IsOctahedral (S i) := by
  sorry

end OMA.S_opg_partitioning_the_projective_plane
