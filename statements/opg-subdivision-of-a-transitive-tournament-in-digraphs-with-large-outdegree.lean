import Mathlib

/-!
# Subdivision of a transitive tournament in digraphs with large outdegree

Source: https://www.openproblemgarden.org/op/subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree
Credit: @ishaanzee

**Conjecture** (W. Mader). For all `k` there is an integer `f(k)` such that every digraph of minimum
outdegree at least `f(k)` contains a subdivision of a transitive tournament of order `k`.

Formalization:
* A digraph on a finite set `V` is a loopless relation `D` (`D u v` is the arc `u → v`); minimum
  outdegree at least `m` means every vertex has at least `m` out-neighbours.
* The transitive tournament of order `k` has vertices `0, …, k - 1` and an arc `i → j` for `i < j`.
  A subdivision of it in `D` consists of distinct branch vertices `b 0, …, b (k - 1)` and, for every
  `i < j`, a directed path `P i j` in `D` from `b i` to `b j` (a list of distinct vertices, each with
  an arc to the next), such that the inner vertices of these paths are not branch vertices and the
  paths for different pairs have no inner vertex in common.
-/

namespace OMA.S_opg_subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree

/-- The inner vertices of a path given as a list (all but the first and the last). -/
def inner {V : Type*} (p : List V) : List V := p.tail.dropLast

/-- `D` contains a subdivision of the transitive tournament of order `k`. -/
def ContainsTTSubdivision {V : Type*} (D : V → V → Prop) (k : ℕ) : Prop :=
  ∃ (b : Fin k → V) (P : Fin k → Fin k → List V), Function.Injective b ∧
    (∀ i j, i < j → (P i j).Nodup ∧ (P i j).head? = some (b i) ∧
      (P i j).getLast? = some (b j) ∧ ∀ a ∈ (P i j).zip (P i j).tail, D a.1 a.2) ∧
    (∀ i j, i < j → ∀ v ∈ inner (P i j), ∀ l, v ≠ b l) ∧
    ∀ i j i' j', i < j → i' < j' → (i, j) ≠ (i', j') → (inner (P i j)).Disjoint (inner (P i' j'))

/-- **Mader's conjecture.** -/
theorem main : ∀ k : ℕ, ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (D : V → V → Prop)
    [DecidableRel D], (∀ v, ¬ D v v) → (∀ v, f ≤ (Finset.univ.filter fun w => D v w).card) →
      ContainsTTSubdivision D k := by
  sorry

end OMA.S_opg_subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree
