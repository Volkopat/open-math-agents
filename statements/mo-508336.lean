import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic

namespace OMA.S_mo_508336

/-- Layers 0, 1 and 2 represent the labels minus one, zero and one, respectively. -/
def cyclicGraph {N : ℕ} (A : Finset (ZMod N)) : SimpleGraph (Fin 3 × ZMod N) :=
  SimpleGraph.fromRel (fun u v =>
    v.1 = 1 ∧
      ((u.1 = 2 ∧ ∃ a ∈ A, v.2 = u.2 - a) ∨
        (u.1 = 0 ∧ ∃ a ∈ A, v.2 = u.2 + a)))

/-- The cyclic three-layer density conjecture for four-cycle-free subgraphs,
with the error tending to zero uniformly as the set of offsets grows. -/
theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (n N : ℕ), n₀ ≤ n → n < N →
      ∀ A : Finset (ZMod N), A.card = n →
      ∀ H : SimpleGraph (Fin 3 × ZMod N), H ≤ cyclicGraph A →
        (SimpleGraph.cycleGraph 4).Free H →
        (H.edgeSet.ncard : ℝ) ≤ (1 / 2 + ε) * ((cyclicGraph A).edgeSet.ncard : ℝ) := by
  sorry

end OMA.S_mo_508336
