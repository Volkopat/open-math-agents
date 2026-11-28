import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# A uniform negative bound for graph eigenvalues

Source: https://mathoverflow.net/questions/362974/upper-bound-for-smallest-eigenvalue-of-infinite-family-of-graphs
Question by Yahav Boneh, 13 June 2020. Formalization credited to @etaubman.

The finite vertex sets are represented by Fin (n i). Regularity, connectedness,
the existence of an edge, and proper induced containment in the next graph are
all retained. A graph embedding preserves and reflects adjacency; failure of
surjectivity makes the induced subgraph proper.

For a finite real symmetric adjacency matrix, saying that some real eigenvalue
is at most c is equivalent to saying that its smallest eigenvalue is at most c.
We use Mathlib's HasEigenvalue, rather than introducing a separate convention
for an indexed minimum. The natural-number indexing starts at zero, which is
only a reindexing of the source's sequence starting at one.
-/

namespace OMA.S_mo_362974

noncomputable def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact G.adjMatrix ℝ

def regular {n : ℕ} (G : SimpleGraph (Fin n)) : Prop := by
  classical
  exact ∃ d : ℕ, G.IsRegularOfDegree d

theorem main :
    ∀ (n : ℕ → ℕ) (G : ∀ i, SimpleGraph (Fin (n i))),
      (∀ i, (G i).Connected) →
      (∀ i, regular (G i)) →
      (∀ i, ∃ u v, (G i).Adj u v) →
      (∀ i, ∃ e : G i ↪g G (i + 1), ¬ Function.Surjective e) →
      ∃ c : ℝ, c < 0 ∧ ∃ N : ℕ, ∀ i, N ≤ i →
        ∃ ev : ℝ, ev ≤ c ∧
          Module.End.HasEigenvalue (adjacency (G i)).mulVecLin ev := by
  sorry

end OMA.S_mo_362974
