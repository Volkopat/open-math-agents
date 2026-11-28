import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1

-- Reduction Arxiv.2001.02665.kotzig_conjecture_large.R1.H1.R1 of step Arxiv.2001.02665.kotzig_conjecture_large.R1.H1
-- Credit: @arindale
--
-- H1 is MPS Case A (Sections 4 & 6): every large tree outside Case C whose pruned core is
-- large and which carries a leaf-matching must admit a rainbow embedding into the
-- near-distance coloured K_{2n+1}.  Unfolding the near-distance condition, the embedding
-- condition says that two edges with equal (undirected) difference are the same edge.
--
-- The reduction splits the statement at the `Sym2` level: H1 is the graceful-labelling core
-- (distinct edges receive distinct undirected differences, stated as vertex-level equality),
-- and H2 is the elementary bridge from vertex-level equality to equality of the `Sym2`
-- classes.  H2 is immediate from `Sym2.eq_iff`; all the mathematical content sits in H1,
-- which is the exact statement a formaliser of Sections 4/6 must produce.

namespace OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H1_R1

open SimpleGraph

/-- Case A graceful labelling, unfolded: distinct edges of `T` get distinct undirected
differences under `g`. -/
def H1 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj],
      T.IsTree →
      n / 100 < (Finset.univ.filter (fun w : Fin (n + 1) =>
        ¬ (T.degree w = 1 ∧ ∃ v, T.Adj v w ∧
          (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 4 ≤
            (Finset.univ.filter (fun u => T.Adj v u ∧ T.degree u = 1)).card))).card →
      (∃ S : Finset (Fin (n + 1)),
        n / (2 ^ Nat.sqrt (Nat.log 2 n)) ^ 6 ≤ S.card ∧
        (∀ x ∈ S, T.degree x = 1) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ T.Adj x y ∧ ∀ z, ¬ (T.Adj x z ∧ T.Adj y z))) →
      ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
        ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
          (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
          (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂)

/-- The `Sym2` bridge: vertex-level equality of two edges yields equality of their edge
classes, hence the rainbow condition. -/
def H2 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj],
    (∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
        (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
        (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂)) →
    ∃ g : Fin (n + 1) ↪ Fin (2 * n + 1),
      ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
        (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
        s(u₁, v₁) = s(u₂, v₂)

theorem main : H1 → H2 → OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1.H1 := by
  intro h1 h2
  filter_upwards [h1] with n hn
  intro T _ hT hcore hS
  obtain ⟨g, hg⟩ := hn T hT hcore hS
  exact h2 n T ⟨g, hg⟩

end OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H1_R1
