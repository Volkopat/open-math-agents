import OMAStatements.S_opg_3_edge_coloring_conjecture

-- Reduction opg-3-edge-coloring-conjecture.R1 of the 3-edge-coloring conjecture (4-flow form).
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the classical digon reduction: if a cubic multigraph with a nowhere-zero 4-flow has two
-- parallel edges e1, e2 between distinct vertices u, v, push the flow of e1 around the 2-cycle
-- e1 e2. Then e1 carries 0 and e2 carries, up to sign, the flow of the third edge at u, which is
-- nonzero and below 4, so G - e1 has a nowhere-zero 4-flow. H2 is the open rest: cubic
-- multigraphs without parallel edges (loops are excluded by any nowhere-zero flow anyway).

namespace OMA.R_opg_3_edge_coloring_conjecture_R1

open OMA.S_opg_3_edge_coloring_conjecture

/-- The digon case: a cubic multigraph with a nowhere-zero 4-flow and two parallel non-loop
edges has an edge `e` such that `G - e` has a nowhere-zero 4-flow. -/
def H1 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
    (∀ v : V, (Finset.univ.filter fun e => src e = v).card +
      (Finset.univ.filter fun e => tgt e = v).card = 3) →
    (∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ src e₁ ≠ tgt e₁ ∧
      ((src e₂ = src e₁ ∧ tgt e₂ = tgt e₁) ∨ (src e₂ = tgt e₁ ∧ tgt e₂ = src e₁))) →
    (∃ f : E → ℤ, (∀ d, 0 < |f d| ∧ |f d| < 4) ∧ IsConservative src tgt f) →
      ∃ e : E, ∃ f : E → ℤ, f e = 0 ∧ (∀ d, d ≠ e → 0 < |f d| ∧ |f d| < 4) ∧
        IsConservative src tgt f

/-- The open core: connected cubic multigraphs with more than two vertices and no two parallel
non-loop edges. -/
def H2 : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V),
    (underlying src tgt).Connected → 2 < Fintype.card V →
    (∀ v : V, (Finset.univ.filter fun e => src e = v).card +
      (Finset.univ.filter fun e => tgt e = v).card = 3) →
    ¬ (∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ src e₁ ≠ tgt e₁ ∧
      ((src e₂ = src e₁ ∧ tgt e₂ = tgt e₁) ∨ (src e₂ = tgt e₁ ∧ tgt e₂ = src e₁))) →
    (∃ f : E → ℤ, (∀ d, 0 < |f d| ∧ |f d| < 4) ∧ IsConservative src tgt f) →
      ∃ e : E, ∃ f : E → ℤ, f e = 0 ∧ (∀ d, d ≠ e → 0 < |f d| ∧ |f d| < 4) ∧
        IsConservative src tgt f

theorem main : H1 → H2 → type_of% @OMA.S_opg_3_edge_coloring_conjecture.main := by
  intro h1 h2 V E _ _ _ src tgt hconn hcard hdeg hflow
  by_cases hd : ∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ src e₁ ≠ tgt e₁ ∧
      ((src e₂ = src e₁ ∧ tgt e₂ = tgt e₁) ∨ (src e₂ = tgt e₁ ∧ tgt e₂ = src e₁))
  · exact h1 V E src tgt hdeg hd hflow
  · exact h2 V E src tgt hconn hcard hdeg hd hflow

end OMA.R_opg_3_edge_coloring_conjecture_R1
