import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2

/-! Split the residual clique-transversal problem at threshold twelve. -/

-- Reduction Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1 of step Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2
-- Credit: @mythintios

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1

/-- The residual clique-transversal bound at threshold twelve. -/
def H1 : Prop :=
  ∀ n, Erdos151.H n = 12 → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- The same graph case at thresholds at least thirteen. -/
def H2 : Prop :=
  ∀ n, 13 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2.H2 := by
  intro htwelve hrest n hn G hG hdegree hedge
  by_cases ht : Erdos151.H n = 12
  · exact htwelve n ht G hG hdegree hedge
  · exact hrest n (by omega) G hG hdegree hedge

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1
