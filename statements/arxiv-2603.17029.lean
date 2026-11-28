import Mathlib

namespace OMA.S_arxiv_2603_17029

/-- A finite simple graph on `Fin n` is edge-regular with parameters `(k, lam)` if it is
`k`-regular and every pair of adjacent vertices has exactly `lam` common neighbors. -/
def IsEdgeRegular {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k lam : ℕ) : Prop :=
  (∀ v : Fin n, (Finset.univ.filter (G.Adj v)).card = k) ∧
  (∀ u v : Fin n, G.Adj u v → (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card = lam)

/-- A Neumaier graph is a connected, non-complete edge-regular graph (with `k ≥ 1`) containing
a nonempty regular clique (a clique `C` such that every vertex outside `C` has the same number
`e` of neighbors in `C`). -/
def IsNeumaierGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  2 ≤ n ∧
  G.Connected ∧
  (∃ u v : Fin n, u ≠ v ∧ ¬ G.Adj u v) ∧
  (∃ k lam : ℕ, 1 ≤ k ∧ IsEdgeRegular G k lam) ∧
  (∃ (C : Finset (Fin n)) (e : ℕ),
    C.Nonempty ∧
    G.IsClique (C : Set (Fin n)) ∧
    ∀ v : Fin n, v ∉ C → (C.filter (G.Adj v)).card = e)

/-- The set of real eigenvalues of the adjacency matrix of `G`. -/
def AdjacencyEigenvalues {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Set ℝ :=
  {μ : ℝ | ∃ v : Fin n → ℝ, v ≠ 0 ∧ (G.adjMatrix ℝ).mulVec v = μ • v}

/--
Open problem from arXiv:2603.17029 (De Bruyn, Evans, Goryainov, Koolen):
Does there exist a Neumaier graph whose adjacency matrix has exactly five distinct eigenvalues?
-/
theorem main :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (inst : DecidableRel G.Adj),
      @IsNeumaierGraph n G inst ∧
      ∃ S : Finset ℝ, S.card = 5 ∧ (S : Set ℝ) = @AdjacencyEigenvalues n G inst := by
  sorry

end OMA.S_arxiv_2603_17029
