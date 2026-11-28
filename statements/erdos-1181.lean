import Mathlib

/-!
# Erdős Problem 1181

Source: https://www.erdosproblems.com/1181
Credit: @mattdorman

The source asks: let `q(n, k)` denote the least prime which does not divide `∏_{1 ≤ i ≤ k} (n + i)`.
Is it true that there exists some `c > 0` such that, for all large `n`,
`q(n, log n) < (1 - c) (log n)²`?

Reading used here: `log` is the natural logarithm and the number of factors is `⌊log n⌋`. Since
`q(n, k)` is the least prime not dividing the product, `q(n, k) < X` holds exactly when some prime
`p < X` does not divide the product; the statement is written in that form, so `q` need not be
defined separately. The statement below is the affirmative answer.
-/

open Filter

namespace OMA.S_erdos_1181

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧
      (p : ℝ) < (1 - c) * Real.log n ^ 2 ∧
      ¬ p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) := by
  sorry

end OMA.S_erdos_1181
