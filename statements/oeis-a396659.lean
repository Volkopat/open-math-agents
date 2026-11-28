import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs

namespace OMA.S_oeis_a396659

/-- An edge-collision walk of length `k` (`k ≥ 1`) starting from vertex `0` on the complete
directed graph with self-loops on `n` labeled vertices (`Fin n`), visiting all `n` vertices. -/
def IsEdgeCollisionWalk (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (w : Fin k → Fin n × Fin n) : Prop :=
  (w ⟨0, by omega⟩).1 = ⟨0, hn⟩ ∧
  (∀ i : Fin k, (hi : i.val + 1 < k) → (w i).2 = (w ⟨i.val + 1, hi⟩).1) ∧
  (∀ i j : Fin (k - 1), i ≠ j → w ⟨i.val, by omega⟩ ≠ w ⟨j.val, by omega⟩) ∧
  (∃ j : Fin (k - 1), w ⟨k - 1, by omega⟩ = w ⟨j.val, by omega⟩) ∧
  (∀ v : Fin n, v = ⟨0, hn⟩ ∨ ∃ i : Fin k, (w i).2 = v)

/-- `T(n, k)` (OEIS A396659): the number of edge-collision walks of length `k` from a fixed
vertex on the complete directed graph with self-loops on `n` labeled vertices that visit all
`n` vertices. -/
noncomputable def T (n k : ℕ) : ℕ :=
  if h : 0 < n ∧ 1 ≤ k then
    letI := Classical.decPred (IsEdgeCollisionWalk n k h.1 h.2)
    (Finset.univ.filter fun w : Fin k → Fin n × Fin n => IsEdgeCollisionWalk n k h.1 h.2 w).card
  else 0

/-- Conjecture (OEIS A396659): `T(n, n^2) / T(n, n^2 + 1) = (2n - 1) / n` for all `n ≥ 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (T n (n ^ 2) : ℚ) / (T n (n ^ 2 + 1) : ℚ) = (2 * (n : ℚ) - 1) / (n : ℚ) := by
  sorry

end OMA.S_oeis_a396659
