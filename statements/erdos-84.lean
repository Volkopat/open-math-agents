import Mathlib

/-!
# Erdős Problem 84

Source: https://www.erdosproblems.com/84
Credit: @mattdorman

The source states (Erdős and Faudree): the cycle set of a graph `G` on `n` vertices is the set
`A ⊆ {3, …, n}` such that `G` has a cycle of length `ℓ` if and only if `ℓ ∈ A`. Let `f(n)` count
the number of possible such `A`. Prove that `f(n) = o(2ⁿ)`. Prove that `f(n) / 2^{n/2} → ∞`.

Reading used here: graphs on `n` vertices are the simple graphs on `Fin n`; `f(n)` is the number
of distinct cycle sets among them. Both requested statements are combined in one conjunction:
`f(n) / 2ⁿ → 0` and `f(n) / 2^{n/2} → ∞`. (The source records that the first part was proved by
Verstraëte.)
-/

open Filter Topology

namespace OMA.S_erdos_84

open Classical in
/-- The cycle set of `G`: the lengths `ℓ ∈ [3, n]` of cycles of `G`. -/
noncomputable def cycleSet {n : ℕ} (G : SimpleGraph (Fin n)) : Finset ℕ :=
  (Finset.Icc 3 n).filter fun l => ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = l

open Classical in
/-- `f(n)`: the number of distinct cycle sets of graphs on `n` vertices. -/
noncomputable def numCycleSets (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (SimpleGraph (Fin n))).image cycleSet).card

theorem main :
    Tendsto (fun n : ℕ => (numCycleSets n : ℝ) / 2 ^ n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (numCycleSets n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2)) atTop atTop := by
  sorry

end OMA.S_erdos_84
