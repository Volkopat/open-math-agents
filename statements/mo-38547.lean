import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Computability.TuringMachine.Computable

/-!
# Efficient computation of a vertex-partition for graphs

Source: Roland Bacher, https://mathoverflow.net/questions/38547, September 2010.
Credit: @LDJAI

We interpret efficient as deterministic polynomial time in the length of
the adjacency-matrix encoding. The output is one bit per vertex. The bit
at vertex zero is fixed to false, resolving the irrelevant global sign.
-/

namespace OMA.S_mo_38547

/-- The complete row-major adjacency matrix; its square length specifies the order. -/
noncomputable def input {n : ℕ} (G : SimpleGraph (Fin (n+1))) : List Bool := by
  classical
  exact (List.ofFn (fun i : Fin (n+1) =>
    List.ofFn (fun j : Fin (n+1) => decide (G.Adj i j)))).flatten

/-- In a rooted spanning tree the sign at a vertex is negative exactly
when its distance from the root is odd. Multiplying all signs adds the
distances modulo two. Spanning trees are subgraphs on the full vertex set. -/
noncomputable def output {n : ℕ} (G : SimpleGraph (Fin (n+1))) : List Bool := by
  classical
  let trees := Finset.univ.filter (fun T : SimpleGraph (Fin (n+1)) => T ≤ G ∧ T.IsTree)
  exact List.ofFn (fun v : Fin (n+1) =>
    decide ((∑ T ∈ trees, T.dist 0 v) % 2 = 1))

/-- One uniform bitstring algorithm works for all connected inputs;
its running time is bounded by one polynomial in the input length. -/
theorem main :
    ∃ solve : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime id id solve) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin (n+1))), G.Connected → solve (input G) = output G := by
  sorry

end OMA.S_mo_38547
