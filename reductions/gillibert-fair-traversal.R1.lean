import OMAStatements.S_gillibert_fair_traversal

-- Reduction gillibert-fair-traversal.R1 of the fair traversal conjecture.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the classical averaging argument: if the automorphism group of G is transitive on edges
-- and G has one Hamiltonian path, the images of that path under all automorphisms cover every
-- edge equally often (complete graphs, cycles, hypercubes, Kneser graphs, ...). It needs neither
-- connectivity nor vertex-transitivity. H2 is the open rest: vertex-transitive graphs that are
-- not edge-transitive or have no Hamiltonian path (the latter is the Lovasz question).

namespace OMA.R_gillibert_fair_traversal_R1

open SimpleGraph OMA.S_gillibert_fair_traversal

/-- Edge-transitive graphs with a Hamiltonian path admit a fair family of Hamiltonian paths. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    2 ≤ Fintype.card V →
    (∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e') →
    (∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian) →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k

/-- The open core: connected vertex-transitive graphs that are not edge-transitive or have no
Hamiltonian path. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
    ¬ ((∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e') ∧
      ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian) →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k

theorem main : H1 → H2 → type_of% @OMA.S_gillibert_fair_traversal.main := by
  intro h1 h2 V _ _ G hc hvt hcard
  by_cases h : (∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ : G ≃g G, Sym2.map φ e = e') ∧
      ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian
  · exact h1 G hcard h.1 h.2
  · exact h2 G hc hvt hcard h

end OMA.R_gillibert_fair_traversal_R1
