import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://mathoverflow.net/questions/383368 -/

open scoped BigOperators

namespace OMA.S_mo_383368

noncomputable def outDegree {n : ℕ} (G : SimpleGraph (Fin n)) (rank : Fin n ≃ Fin n)
    (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w => G.Adj v w ∧ rank v < rank w).card

noncomputable def inDegree {n : ℕ} (G : SimpleGraph (Fin n)) (rank : Fin n ≃ Fin n)
    (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w => G.Adj v w ∧ rank w < rank v).card

/-- The minimum mixed-degree sum is at most the minimum squared out-degree sum.
Equivalently, every ordering on the right admits some ordering on the left. -/
theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (rank : Fin n ≃ Fin n),
    ∃ rank' : Fin n ≃ Fin n,
      (∑ v, outDegree G rank' v * inDegree G rank' v) ≤ ∑ v, (outDegree G rank v) ^ 2 := by
  sorry

end OMA.S_mo_383368
