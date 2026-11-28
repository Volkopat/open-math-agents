import FormalConjectures.Paper.KotzigConjecture
import Mathlib

/-!
Reduction KotzigConjecture.kotzig_conjecture.R1: split by the maximum degree of the tree.

H1 is the classical path case: every tree of maximum degree at most 2 (a path with `n` edges)
decomposes `K_{2n+1}` by cyclic shifts of one embedding. This is Rosa's 1967 theorem: the zigzag
labelling `0, n, 1, n - 1, 2, ...` of the path is graceful (its edge lengths are `n, n - 1, ..., 1`),
and the `2n + 1` cyclic shifts of a labelling with distinct lengths in `{1, ..., n}` partition the
edges of `K_{2n+1}`. A known case, not progress on the conjecture.

H2 is the open remainder: trees with a vertex of degree at least 3.
-/

namespace OMA.R_KotzigConjecture_kotzig_conjecture_R1

open SimpleGraph

/-- Kotzig's conjecture for paths (trees of maximum degree at most 2). -/
def H1 : Prop :=
  ∀ {V : Type} [Finite V] (T : SimpleGraph V), T.IsTree →
    (∀ v, (T.neighborSet v).ncard ≤ 2) →
    ∀ (n : ℕ), T.edgeSet.ncard = n →
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))

/-- The open remainder: trees with a vertex of degree at least 3. -/
def H2 : Prop :=
  ∀ {V : Type} [Finite V] (T : SimpleGraph V), T.IsTree →
    (∃ v, 2 < (T.neighborSet v).ncard) →
    ∀ (n : ℕ), T.edgeSet.ncard = n →
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))

theorem main : H1 → H2 → type_of% @KotzigConjecture.kotzig_conjecture := by
  intro h1 h2 V _ T hT n hn
  by_cases h : ∀ v, (T.neighborSet v).ncard ≤ 2
  · exact h1 T hT h n hn
  · simp only [not_forall, not_le] at h
    exact h2 T hT h n hn

end OMA.R_KotzigConjecture_kotzig_conjecture_R1
