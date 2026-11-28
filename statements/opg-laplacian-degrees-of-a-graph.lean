import Mathlib

/-!
# Laplacian Degrees of a Graph

Source: https://www.openproblemgarden.org/op/laplacian_degrees_of_a_graph
Credit: @mburv

Conjecture (J.-M. Guo): if `G` is a connected graph on `n` vertices, then `c_k(G) ≥ d_k(G)` for
`k = 1, 2, …, n - 1`.

Definitions from the source: `L = D - A` is the Laplacian matrix of `G` (Mathlib's
`SimpleGraph.lapMatrix`), `t_k` is the `k`-th largest eigenvalue of `L` (`k = 1, …, n`), the
`k`-th Laplacian degree is `c_k = t_k + k - 2`, and `d_k` is the `k`-th largest vertex degree.

Encoding: graphs are simple graphs on `Fin n`. The eigenvalues of the real symmetric matrix `L`,
counted with multiplicity, are the roots of its characteristic polynomial (which splits over `ℝ`);
`t_k` is entry `k - 1` of that multiset of roots sorted in nonincreasing order. Likewise `d_k` is
entry `k - 1` of the multiset of vertex degrees sorted in nonincreasing order. Both are only used
for `1 ≤ k ≤ n - 1`, where the index is in range.

Literature note (not part of the statement): A. E. Brouwer and W. H. Haemers, A lower bound for
the Laplacian eigenvalues of a graph - proof of a conjecture by Guo, Linear Algebra Appl. 429
(2008), 2131-2135, prove this (`μ_j ≥ d_j - j + 2` for connected graphs, `1 ≤ j ≤ n - 1`).
-/

namespace OMA.S_opg_laplacian_degrees_of_a_graph

/-- `t_k`: the `k`-th largest eigenvalue (with multiplicity) of the Laplacian matrix `D - A`,
for `1 ≤ k ≤ n`. -/
noncomputable def laplacianEigenvalue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : ℝ :=
  ((G.lapMatrix ℝ).charpoly.roots.sort (· ≥ ·)).getD (k - 1) 0

/-- `d_k`: the `k`-th largest vertex degree of `G`, for `1 ≤ k ≤ n`. -/
def kthLargestDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)).getD (k - 1) 0

/-- Guo's conjecture: for a connected graph on `n` vertices, the `k`-th Laplacian degree
`c_k = t_k + k - 2` is at least the `k`-th largest degree `d_k`, for `k = 1, …, n - 1`. -/
theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      (kthLargestDegree G k : ℝ) ≤ laplacianEigenvalue G k + k - 2 := by
  sorry

end OMA.S_opg_laplacian_degrees_of_a_graph
