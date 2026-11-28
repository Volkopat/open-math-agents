import Mathlib.Combinatorics.Digraph.Basic

/-!
# The Laborde–Payan–Xuong conjecture

Open Problem Garden:
https://www.openproblemgarden.org/op/stable_set_meeting_all_longest_directed_paths

J. M. Laborde, C. Payan, and N. H. Xuong, *Independent sets and longest directed paths in
digraphs*, Graphs and Other Combinatorial Topics, Teubner-Texte Math. 59 (1983), 173–177.
-/

namespace OMA.S_opg_stable_set_meeting_all_longest_directed_paths

/-- A directed path with `n` arcs is a sequence of `n + 1` distinct vertices
with an arc from each vertex to its successor. -/
def IsDirectedPath {V : Type*} (D : Digraph V) {n : ℕ} (p : Fin (n + 1) → V) : Prop :=
  Function.Injective p ∧ ∀ i : Fin n, D.Adj (p i.castSucc) (p i.succ)

/-- Every finite loopless digraph has a stable set meeting every longest directed path.
The same set must meet all paths whose length is maximum among directed paths in the graph. -/
theorem main :
    ∀ {V : Type*} [Finite V] (D : Digraph V), (∀ v, ¬ D.Adj v v) →
      ∃ S : Set V, S.Pairwise (fun u v => ¬ D.Adj u v) ∧
        ∀ (n : ℕ) (p : Fin (n + 1) → V), IsDirectedPath D p →
          (∀ (m : ℕ) (q : Fin (m + 1) → V), IsDirectedPath D q → m ≤ n) →
          ∃ i, p i ∈ S := by
  sorry

end OMA.S_opg_stable_set_meeting_all_longest_directed_paths
