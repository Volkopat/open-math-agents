import OMAStatements.S_mo_153208
import Mathlib

/-! The subgraph poset of graphs on `n` vertices is graded by the number of edges. The
classical part of the question: a map `φ` that preserves and reflects the subgraph order
`Sub` preserves the number of edges of every graph. An injective homomorphism `G →g H`
between graphs on `Fin n` maps edges injectively to edges, so `Sub G H` gives
`|E(G)| ≤ |E(H)|`, with equality only if `H` and `G` are isomorphic; every graph is reached
from the empty graph by adding one edge at a time and reaches the complete graph that way, and
`φ` maps such chains to strict chains, which gives `|E(φ G)| ≥ |E(G)|` and
`|E(φ G)| ≤ |E(G)|`. The open rest: an automorphism of the graded poset that preserves the
rank is trivial for `n ≥ 5`. -/

namespace OMA.R_mo_153208_R1

open OMA.S_mo_153208

/-- An order automorphism of the subgraph order preserves the number of edges. -/
def H1 : Prop :=
  ∀ n : ℕ, ∀ φ : SimpleGraph (Fin n) → SimpleGraph (Fin n),
    (∀ G H : SimpleGraph (Fin n), Sub G H ↔ Sub (φ G) (φ H)) →
    ∀ G : SimpleGraph (Fin n), (φ G).edgeSet.ncard = G.edgeSet.ncard

/-- The open rest: a rank-preserving automorphism is trivial. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ φ : SimpleGraph (Fin n) → SimpleGraph (Fin n),
    (∀ G H : SimpleGraph (Fin n), Sub G H ↔ Sub (φ G) (φ H)) →
    (∀ H : SimpleGraph (Fin n), ∃ G, Nonempty (φ G ≃g H)) →
    (∀ G : SimpleGraph (Fin n), (φ G).edgeSet.ncard = G.edgeSet.ncard) →
    ∀ G : SimpleGraph (Fin n), Nonempty (φ G ≃g G)

theorem main : H1 → H2 → type_of% @OMA.S_mo_153208.main := by
  intro h1 h2 n hn φ hφ hs
  exact h2 n hn φ hφ hs (h1 n φ hφ)

end OMA.R_mo_153208_R1
