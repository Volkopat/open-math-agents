import Mathlib

/-!
# Spanning trees and path forests in infinite vertex-transitive graphs

Source: Agelos, https://mathoverflow.net/questions/440608
Credit: @wtho704

The three clauses are the leafless spanning tree, the spanning forest of
rays and the spanning forest of double-rays, in that order. A forest of
paths is specified by a bijection from its component-and-position pairs
to the vertices, with an edge between successive positions in each path.
-/

namespace OMA.S_mo_440608

open SimpleGraph
universe u

theorem main :
    ∀ (V : Type u) [Infinite V] (G : SimpleGraph V),
      G.Connected →
      (∀ v, (G.neighborSet v).Finite) →
      (∀ v w, ∃ f : G ≃g G, f v = w) →
      (∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∀ v, ¬ (∃! w, T.Adj v w)) ∧
      (∃ (C : Type u) (e : C × ℕ ≃ V), ∀ c i, G.Adj (e (c, i)) (e (c, i + 1))) ∧
      (∃ (C : Type u) (e : C × ℤ ≃ V), ∀ c i, G.Adj (e (c, i)) (e (c, i + 1))) := by
  sorry

end OMA.S_mo_440608
