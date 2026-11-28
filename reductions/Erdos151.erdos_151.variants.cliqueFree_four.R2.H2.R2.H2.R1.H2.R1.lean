import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1

-- Reduction Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H2.R1 of step Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H2.R1.H2
-- Credit: @wispiANt

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H2_R1

/-- Count lone edges incident to an independent set when every free set has size at most D.
The excess sum counts repeated lone neighbors beyond the second incidence. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    ∀ D : ℕ, n ≤ cliqueTransversalNumber G + D →
    let lone := fun (x y : Fin n) => G.Adj x y ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z
    ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
      2 * n + (D + 1) * I.card + (D - G.indepNum) +
          (∑ x : Fin n, ((I.filter (lone x)).card - 2)) ≤
        (D + 4) * D + ∑ x ∈ I, (univ.filter (lone x)).card

/-- The remaining threshold problem for graphs satisfying the independent-set count. -/
def H2 : Prop :=
  ∀ (n : ℕ), 13 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    let D := Erdos151.H n - 1
    (let lone := fun (x y : Fin n) => G.Adj x y ∧ ¬ ∃ z, G.Adj x z ∧ G.Adj y z
      ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) →
        2 * n + (D + 1) * I.card + (D - G.indepNum) +
            (∑ x : Fin n, ((I.filter (lone x)).card - 2)) ≤
          (D + 4) * D + ∑ x ∈ I, (univ.filter (lone x)).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1.H2 := by
  intro hcount hremaining n hn G hG hdegree hcommon
  by_contra hbad
  apply hbad
  apply hremaining n hn G hG hdegree hcommon
  exact hcount n G hG (Erdos151.H n - 1) (by omega)

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R2_H2_R1_H2_R1
