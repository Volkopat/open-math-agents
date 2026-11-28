import Mathlib.Logic.Function.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace OMA.S_wpc_k_server_conjecture

/-- Each request places the chosen server at the requested point and incurs the distance
from its current location. The policy sees the served prefix and the current request. -/
noncomputable def serveCost {M : Type*} [MetricSpace M] {k : ℕ}
    (policy : List M → M → Fin k) (locations : Fin k → M)
    (served : List M) : List M → ℝ
  | [] => 0
  | request :: rest =>
      let server := policy served request
      dist (locations server) request +
        serveCost policy (Function.update locations server request) (served ++ [request]) rest

/-- On any metric space with more than k points, k servers have a deterministic
online policy with competitive ratio k, up to an additive constant. -/
theorem main :
    ∀ (M : Type*) [MetricSpace M] (k : ℕ), 0 < k →
      Nonempty (Fin (k + 1) ↪ M) →
        ∀ initial : Fin k → M,
          ∃ (online : List M → M → Fin k) (constant : ℝ),
            0 ≤ constant ∧
              ∀ (requests : List M) (other : List M → M → Fin k),
                serveCost online initial [] requests ≤
                  (k : ℝ) * serveCost other initial [] requests + constant := by
  sorry

end OMA.S_wpc_k_server_conjecture
