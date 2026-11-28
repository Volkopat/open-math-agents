import Mathlib

/-!
# Seagull problem

Source: https://www.openproblemgarden.org/op/seagull_problem
Credit: @lzvxck

The source (attributed to Seymour): every `n` vertex graph with no independent set of size 3
has a complete graph on `⌈n/2⌉` vertices as a minor.

`⌈n/2⌉` is `(n + 1) / 2` in natural-number division. `G` has `K_m` as a minor exactly when
there are `m` pairwise disjoint, nonempty vertex sets (branch sets), each inducing a connected
subgraph, with an edge of `G` between every two of them.
-/

namespace OMA.S_opg_seagull_problem

/-- `G` has the complete graph on `m` vertices as a minor: there are `m` pairwise disjoint,
nonempty, connected branch sets, any two of which are joined by an edge of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ B : Fin m → Set V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- **Seagull problem.** Every graph on `n` vertices with no independent set of size 3 has
`K_⌈n/2⌉` as a minor. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IndepSetFree 3 →
    HasCompleteMinor G ((Fintype.card V + 1) / 2) := by
  sorry

end OMA.S_opg_seagull_problem
