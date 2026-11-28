import Mathlib

/-!
# Distances between orthocenters of triangles with concyclic vertices

Source: https://mathoverflow.net/questions/377077
Asked by MathOverflow user cristi0p (Weird geometry problem I found).

Let `n ≥ 4` and let `A_1, ..., A_n` be concyclic points. Consider the orthocenters
`H_1, H_2, ...` of the triangles determined by these points. The question asks to show
`∑_{H_a, H_b} H_a H_b ≥ (n - 2)(n - 3)/2 · ∑_{1 ≤ i, j ≤ n} A_i A_j`
(lengths of segments), and to determine the equality case.

Translation choices.
* The plane is `ℂ`, distances are `‖z - w‖`. The points are `A : Fin n → ℂ`, pairwise
  distinct (`Function.Injective A`), and concyclic: all at the same distance `r` from a
  common center `O`.
* The triangles determined by the points are the `3`-element subsets `t` of `Fin n`. The
  orthocenters are given by an arbitrary function `H` on these subsets, required to satisfy
  the defining property of the orthocenter: for every vertex `A i` of `t`, the vector
  `H t - A i` is orthogonal to the opposite side `A j - A k`. Orthogonality of `u, v ∈ ℂ` is
  the vanishing of the real dot product `(u * conj v).re`. (For a nondegenerate triangle
  this determines the orthocenter uniquely.)
* Orthocenters are indexed by triangles, i.e. counted with multiplicity, one for each of the
  `n choose 3` triangles. Both sums run over ordered pairs, as written: on the left over
  ordered pairs of triangles, on the right over all `1 ≤ i, j ≤ n` (the diagonal terms are
  zero).
* Only the inequality is formalized, not the description of the equality case.
-/

namespace OMA.S_mo_377077

/-- `H` is the orthocenter of the triangle with vertices `A i`, `i ∈ t`: for any vertex, the
line from it to `H` is perpendicular to the opposite side. -/
def IsOrthocenter {n : ℕ} (A : Fin n → ℂ) (t : Finset (Fin n)) (H : ℂ) : Prop :=
  ∀ i ∈ t, ∀ j ∈ t, ∀ k ∈ t, i ≠ j → i ≠ k → j ≠ k →
    ((H - A i) * (starRingEnd ℂ) (A j - A k)).re = 0

theorem main :
    ∀ n : ℕ, 4 ≤ n → ∀ A : Fin n → ℂ, Function.Injective A →
      (∃ O : ℂ, ∃ r : ℝ, ∀ i, ‖A i - O‖ = r) →
      ∀ H : Finset (Fin n) → ℂ,
        (∀ t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, IsOrthocenter A t (H t)) →
        ((n : ℝ) - 2) * ((n : ℝ) - 3) / 2 * ∑ i, ∑ j, ‖A i - A j‖ ≤
          ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
            ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, ‖H s - H t‖ := by
  sorry

end OMA.S_mo_377077
