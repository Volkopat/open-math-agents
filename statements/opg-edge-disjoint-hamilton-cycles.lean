import Mathlib

/-!
# Edge-disjoint Hamilton cycles in highly strongly connected tournaments

Source: https://www.openproblemgarden.org/op/edge_disjoint_hamilton_cycles
Credit: @ishaanzee

**Conjecture** (C. Thomassen). For every `k ≥ 2`, there is an integer `f(k)` so that every strongly
`f(k)`-connected tournament has `k` edge-disjoint Hamilton cycles.

Formalization:
* A tournament on a finite set `V` is a relation `T` with no loops and exactly one of `T u v`,
  `T v u` for distinct `u`, `v`.
* Strongly `m`-connected: more than `m` vertices, and after deleting any set of fewer than `m`
  vertices the remaining tournament is strongly connected (every remaining vertex reaches every
  other through remaining vertices).
* A Hamilton cycle is an enumeration `e : Fin n ≃ V` of the `n = |V|` vertices with arcs
  `e i → e (i + 1 mod n)` (`finRotate`); its arcs are these `n` pairs. The `k` Hamilton cycles
  are edge-disjoint when no arc is used by two of them.
-/

namespace OMA.S_opg_edge_disjoint_hamilton_cycles

/-- `T` is strongly `m`-connected. -/
def IsStronglyConnectedOfOrder {V : Type*} [Fintype V] (T : V → V → Prop) (m : ℕ) : Prop :=
  m < Fintype.card V ∧ ∀ S : Finset V, S.card < m → ∀ x y : V, x ∉ S → y ∉ S →
    Relation.ReflTransGen (fun a b => T a b ∧ a ∉ S ∧ b ∉ S) x y

/-- **Thomassen's conjecture.** -/
theorem main : ∀ k : ℕ, 2 ≤ k → ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (T : V → V → Prop), (∀ v, ¬ T v v) → (∀ u v, u ≠ v → (T u v ↔ ¬ T v u)) →
    IsStronglyConnectedOfOrder T f →
      ∃ H : Fin k → (Fin (Fintype.card V) ≃ V),
        (∀ i m, T (H i m) (H i (finRotate _ m))) ∧
        ∀ i j, i ≠ j → ∀ m m', ¬ (H i m = H j m' ∧ H i (finRotate _ m) = H j (finRotate _ m')) := by
  sorry

end OMA.S_opg_edge_disjoint_hamilton_cycles
