import Mathlib

namespace OMA.S_mo_26890

/-- An undirected trail can visit any ordered list of k + 1 distinct vertices
in a k-edge-connected graph. -/
theorem main :
    ∀ (k n : ℕ), 0 < k →
      ∀ G : SimpleGraph (Fin n), G.IsEdgeConnected k →
        ∀ terminals : Fin (k + 1) ↪ Fin n,
          ∃ (a b : Fin n) (walk : G.Walk a b),
            walk.IsTrail ∧
              (List.ofFn (fun i : Fin (k + 1) => terminals i)).Sublist walk.support := by
  sorry

end OMA.S_mo_26890
