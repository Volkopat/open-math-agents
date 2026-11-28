import Mathlib

/-!
# Erdős Problem 1016

Source: https://www.erdosproblems.com/1016
Credit: @mattdorman

The source asks (a problem of Bondy): let `h(n)` be minimal such that there is a graph on `n`
vertices with `n + h(n)` edges which contains a cycle on `k` vertices for all `3 ≤ k ≤ n`
(a pancyclic graph). Is it true that `h(n) ≥ log₂ n + log_* n - O(1)`, where `log_*` is the
iterated logarithm?

Reading used here: graphs on `n` vertices are simple graphs on `Fin n`. Since `h(n)` is minimal,
`h(n) ≥ X` says that every pancyclic graph on `n` vertices has at least `n + X` edges; the
statement asks for one constant `C` that works for all `n ≥ 3`. `log_* n` is the number of times
the base-2 logarithm must be applied to bring `n` down to at most `1`; it is computed here with
the integer logarithm `Nat.log 2`, which changes `log_*` by a bounded amount only and so is
absorbed in `O(1)`. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_1016

/-- The iterated base-2 logarithm. -/
def logStar (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0 else 1 + logStar (Nat.log 2 n)
decreasing_by exact Nat.log_lt_self 2 (by omega)

/-- `G` contains a cycle of every length from `3` to the number of vertices. -/
def IsPancyclic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k, 3 ≤ k → k ≤ n → ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = k

theorem main :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ G : SimpleGraph (Fin n), IsPancyclic G →
      (n : ℝ) + Real.logb 2 n + logStar n - C ≤ G.edgeSet.ncard := by
  sorry

end OMA.S_erdos_1016
