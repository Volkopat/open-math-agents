import Mathlib

namespace OMA.S_mo_99770

/-- Every cycle has length at least six, including the acyclic case. -/
def HasGirthAtLeastSix {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (v : Fin n) (cycle : G.Walk v v), cycle.IsCycle → 6 ≤ cycle.length

def IsExtremal {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  HasGirthAtLeastSix G ∧
    ∀ H : SimpleGraph (Fin n), HasGirthAtLeastSix H →
      H.edgeSet.ncard ≤ G.edgeSet.ncard

/-- Is there an order at which every graph maximizing the edge count
subject to girth at least six is nonbipartite? -/
theorem main :
    ∃ n : ℕ, 0 < n ∧
      ∀ G : SimpleGraph (Fin n), IsExtremal G → ¬ G.Colorable 2 := by
  sorry

end OMA.S_mo_99770
