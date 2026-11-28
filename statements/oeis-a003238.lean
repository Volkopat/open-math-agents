import Mathlib

/-!
# OEIS A003238: level-regular rooted trees, growth of `log a(n)`

Source: https://oeis.org/A003238
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of rooted trees with `n` vertices in which vertices at the same level have
the same degree. Conjecture (OEIS entry, Formula section): `log a(n)` is asymptotic to
`c · log(n)²` for some `0.4 < c < 0.5`. (The entry notes that `log a(n) ~ log(n)² / log 4` has
since been shown, so the conjecture is only partly correct; `main` states it as conjectured.)

Conventions:
* Such a tree is determined by the numbers `d₁, d₂, …, d_k ≥ 1` of children of each vertex at
  levels `0, 1, …, k-1` (the last level has no children), and then has
  `1 + d₁ + d₁d₂ + ⋯ + d₁⋯d_k` vertices. So `a(n)` counts finite sequences of positive integers
  with that sum equal to `n`; for `n ≥ 1` every entry is `≤ n`, so we count lists over
  `{1, …, n}` of length `< n`.
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`.
-/

namespace OMA.S_oeis_a003238

open Filter Asymptotics

/-- Number of vertices `1 + d₁ + d₁d₂ + ⋯` of the level-regular tree with child counts `ds`. -/
def size : List ℕ → ℕ
  | [] => 1
  | d :: ds => 1 + d * size ds

/-- `a(n)`: number of level-regular rooted trees with `n` vertices, i.e. of sequences
`(d₁, …, d_k)` (`k < n`, `1 ≤ dᵢ ≤ n`) with `size = n`; `f i + 1` is `dᵢ₊₁`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ((Finset.univ : Finset (Fin k → Fin n)).filter
    fun f => size (List.ofFn fun i => (f i : ℕ) + 1) = n).card

/-- `log a(n) ~ c log(n)²` for some `0.4 < c < 0.5`. -/
theorem main : ∃ c : ℝ, 0.4 < c ∧ c < 0.5 ∧
    IsEquivalent atTop (fun n : ℕ => Real.log (a n)) (fun n => c * Real.log n ^ 2) := by
  sorry

end OMA.S_oeis_a003238
